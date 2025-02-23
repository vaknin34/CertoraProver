/*
 *     The Certora Prover
 *     Copyright (C) 2025  Certora Ltd.
 *
 *     This program is free software: you can redistribute it and/or modify
 *     it under the terms of the GNU General Public License as published by
 *     the Free Software Foundation, version 3 of the License.
 *
 *     This program is distributed in the hope that it will be useful,
 *     but WITHOUT ANY WARRANTY; without even the implied warranty of
 *     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *     GNU General Public License for more details.
 *
 *     You should have received a copy of the GNU General Public License
 *     along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package normalizer

import analysis.CmdPointer
import analysis.icfg.SummaryStack
import analysis.icfg.SummaryStack.START_EXTERNAL_SUMMARY
import analysis.icfg.SummaryStack.START_INTERNAL_SUMMARY
import analysis.ip.INTERNAL_FUNC_START
import analysis.ip.InternalFuncStartAnnotation
import datastructures.stdcollections.*
import analysis.storage.DisplayPath
import ksp.dynamicconversion.uncheckedAs
import log.Logger
import log.LoggerTypes
import tac.MetaKey
import tac.MetaMap
import vc.data.TACCmd.Simple.AnnotationCmd.Annotation
import vc.data.*
import vc.data.SnippetCmd.CVLSnippetCmd.*
import vc.data.SnippetCmd.EVMSnippetCmd.*
import vc.data.TACCmd.Simple.AnnotationCmd
import java.io.Serializable

/**
 * A utility function to warn in case of failed patching or invariant check-failure
 **/
private fun <T> T?.warnIf(
    logger: Logger,
    predicate: (T?) -> Boolean = { it == null },
    f: () -> String
): T? = apply {
    if (predicate(this)) {
        logger.warn(f)
    }
}

/**
 * For each non-canonical command or meta-value - of [NonCanonValue.Meta] [NonCanonValue.Annotation] [NonCanonValue.Message]
 * marks its meta-map with a corresponding [MetaKey] mapped to a unique Int
 * defined by DFS traversal order [CoreTACProgram.dfs]
 *
 * and build a mapping table of
 * ```
 * Int -> NonCanonValue
 * ```
 *
 * Used when caching [CoreTACProgram] needs a meaningful counter-example,
 * by the following logic
 * [annotator] - returns a [DefaultTACCmdMapper] that builds [NonCanonicalTranslationTable] while annotating when `map` is called
 *
 * [patcher] - returns a [DefaultTACCmdMapper] that for each [TACCmd]/[vc.data.TACSymbol.Var] with a [NonCanonValue],
 * it tries to replace it with a value in [NonCanonMapper]
 *
 * So a cached [CoreTACProgram] with the same topology, i.e. [CoreTACProgram.digest] is equal
 * as a given on should have corresponding [MetaKey] mapped to the same IDs
 */
class NonCanonicalTranslationTable(val logger: Logger) {
    val metaState = NonCanonMapper<NonCanonValue.Meta>("non-canonical-meta")
    val annotationState = NonCanonMapper<NonCanonValue.Annotation>("non-canonical-annotation")
    val messageState = NonCanonMapper<NonCanonValue.Message>("non-canonical-message")

    fun NonCanonValue.put() = when (this) {
        is NonCanonValue.Meta -> metaState.put(this)
        is NonCanonValue.Annotation -> annotationState.put(this)
        is NonCanonValue.Message -> messageState.put(this)
    }

    fun NonCanonValue.key(): MetaKey<Int> = state().nonCanonicalKey

    private fun NonCanonValue.state() = when (this) {
        is NonCanonValue.Meta -> metaState
        is NonCanonValue.Annotation -> annotationState
        is NonCanonValue.Message -> messageState
    }

    companion object {
        operator fun invoke(ctp: CoreTACProgram, logger: Logger = Logger(LoggerTypes.NORMALIZER)) =
            NonCanonicalTranslationTable(logger).run {
                val (annotateProgram, duration) = kotlin.time.measureTimedValue {
                    annotate(ctp, logger)
                }
                logger.info { "Time for scanning command-graph: ${duration.inWholeMilliseconds} milli-seconds" }
                annotateProgram to this
            }
    }

    private fun annotate(ctp: CoreTACProgram, logger: Logger): CoreTACProgram = ctp.patching {
        ctp.dfs { nbid, commands ->
            for ((index, cmd) in commands.withIndex()) {
                unorderedVarAccess(cmd)?.warnIf(logger) { "visit $it as part of $cmd: canonical order is not guaranteed" }
                it.replaceCommand(CmdPointer(nbid, index), listOf(annotator.map(cmd)))
            }
        }
    }

    fun patch(ctp: CoreTACProgram): CoreTACProgram = ctp.patching {
        ltacStream().forEach { (ptr, cmd) -> it.replaceCommand(ptr, listOf(patcher.map(cmd))) }
    }


    /**
     *  insert to [TACCmd] or [vc.data.TACSymbol.Var] [MetaMap] a [MetaKey] -> [Int] indicating that there is a non-canonical value that should be patched in [patch]
     *  and insert the same [Int] -> [NonCanonValue] in the corresponding [NonCanonMapper.nonCanonValues]
     **/
    private val annotator = object : DefaultTACCmdMapper() {
        /** if [meta] is not marked as [NonCanonMapper.nonCanonicalKey] and has non-canonical meta-data insert it to [NonCanonMapper.nonCanonValues] */
        private fun annotateNonCanonValue(meta: MetaMap, nonCanonValue: NonCanonValue) =
            if (nonCanonValue.key() !in meta && nonCanonValue.hasNonCanonical()) {
                val id = nonCanonValue.put()
                meta.plus(nonCanonValue.key() to id)
            } else {
                meta
            }

        private fun annotateMetaMap(t: MetaMap): MetaMap =
            annotateNonCanonValue(t, NonCanonValue.meta(t))

        override fun mapAnnotationCmd(t: AnnotationCmd): TACCmd.Simple =
            super.mapAnnotationCmd(t)
                .mapMeta { annotateNonCanonValue(it, NonCanonValue.Annotation(t.annot)) }

        override fun mapAssertCmd(t: TACCmd.Simple.AssertCmd): TACCmd.Simple =
            super.mapAssertCmd(t)
                .mapMeta { annotateNonCanonValue(it, NonCanonValue.Message(t.msg)) }

        override fun mapLabelCmd(t: TACCmd.Simple.LabelCmd): TACCmd.Simple =
            super.mapLabelCmd(t)
                .mapMeta { annotateNonCanonValue(it, NonCanonValue.Message(t._msg)) }

        override fun mapMeta(t: MetaMap): MetaMap = super.mapMeta(annotateMetaMap(t))
    }

    /** returns [TACCmdMapper] that's build from [NonCanonMapper.nonCanonValues]
     * where when we find a non-canonical meta with try to replace it with an entry with the same ID **/
    private val patcher = object : DefaultTACCmdMapper() {
        private fun getMsg(t: TACCmd.Simple) =
            messageState.get(t.meta)?.msg.warnIf(logger) { "could not patch $t message" }

        private fun getAnnot(t: AnnotationCmd) =
            annotationState.get(t.meta)?.annot?.let { t.annot.patch(it, logger) }

        private fun patchMeta(t: MetaMap): MetaMap =
            metaState.get(t)?.meta?.let { t.patch(it, logger) } ?: t

        override fun mapAnnotationCmd(t: AnnotationCmd): TACCmd.Simple =
            super.mapAnnotationCmd(getAnnot(t)?.let { t.copy(annot = it) } ?: t)

        override fun mapAssertCmd(t: TACCmd.Simple.AssertCmd): TACCmd.Simple =
            super.mapAssertCmd(getMsg(t)?.let { t.copy(description = it) } ?: t)

        override fun mapLabelCmd(t: TACCmd.Simple.LabelCmd): TACCmd.Simple =
            super.mapLabelCmd(getMsg(t)?.let { t.copy(_msg = it) } ?: t)

        override fun mapMeta(t: MetaMap): MetaMap = super.mapMeta(patchMeta(t))
    }
}


/**
 * patch [this] [MetaMap] taken from cached [TACProgram] by [patchesFromCurrentRun]
 * taken from [NonCanonicalTranslationTable.annotationState], or [NonCanonicalTranslationTable.metaState]
 *
 * of current-runs [NonCanonicalTranslationTable],
 *
 * For all [MetaKey] in [patchesFromCurrentRun], [MetaKey.restore] == true
 * So it is fine for a [MetaKey] in [this] to not be in [patchesFromCurrentRun]
 *
 **/
fun MetaMap.patch(patchesFromCurrentRun: MetaMap, logger: Logger) = updateValues { (k, v) ->
    patchesFromCurrentRun[k].warnIf(
        logger,
        { k.restore && it == null }) { "could not patch $k from $this and patches $patchesFromCurrentRun" }
        ?.let {
            /** v and it came from a [MetaMap], it is safe to assume their correctness **/
            @Suppress("Treapability")
            Annotation(k, v).patch(Annotation(k, it), logger)?.v
        }
        ?: v
}

sealed interface NonCanonValue : Serializable {
    /**
     * holds a [MetaMap] of non-canonical values
     **/
    data class Meta(val meta: MetaMap) : NonCanonValue, Serializable

    data class Annotation(val annot: AnnotationCmd.Annotation<*>) : NonCanonValue, Serializable

    data class Message(val msg: String) : NonCanonValue, Serializable

    fun hasNonCanonical(): Boolean = when (this) {
        is Meta -> meta.map.isNotEmpty()
        is Annotation -> annot.k.restore
        is Message -> true
    }

    companion object {
        fun meta(meta: MetaMap): Meta = Meta(meta.filter { it.key.restore })
    }
}

class NonCanonMapper<V : NonCanonValue>(nonCanonicalKeyName: String) {
    val nonCanonicalKey = MetaKey<Int>(nonCanonicalKeyName)
    private val nonCanonValues: MutableList<V> = mutableListOf()

    fun get(meta: MetaMap) = meta[nonCanonicalKey]?.let { nonCanonValues.getOrNull(it) }
    fun put(t: V): Int {
        nonCanonValues.add(t)
        return nonCanonValues.lastIndex
    }
}

/**
 * given an [AnnotationCmd.Annotation] of a [CoreTACProgram] and another [AnnotationCmd.Annotation]
 * taken from a [NonCanonicalTranslationTable.annotationState], or [NonCanonicalTranslationTable.metaState],
 * generated from an isomorphic [CoreTACProgram] (as defined by [CoreTACProgram.digest])
 *
 * return a [AnnotationCmd.Annotation] that is constructed from
 * * non-canonical values of [fromCurrentRunTable], for example: meta-values that are indexed by [TACMeta.CVL_RANGE] [TACMeta.CVL_DISPLAY_NAME]
 * * canonical-values of [this], for example [TACSymbol] and meta-values annotated by [allocator.GeneratedBy]
 **/
private fun Annotation<*>.patch(
    fromCurrentRunTable: Annotation<*>,
    logger: Logger
): Annotation<*>? =
    when {
        k != fromCurrentRunTable.k -> null
        // in case we have different subclasses, for example [SnippetCmd]
        v::class != fromCurrentRunTable.v::class -> null
        // different [displayPath] structure means we might not be able to [merge]
        v is StorageSnippet
            && fromCurrentRunTable.v is StorageSnippet
            && !v.displayPath.structuralCheck(fromCurrentRunTable.v.displayPath) -> null
        // different number of arguments mean we cannot [merge]
        v is InternalFuncStartAnnotation && fromCurrentRunTable.v is InternalFuncStartAnnotation && v.args.size != fromCurrentRunTable.v.args.size -> null
        else -> when (v) {
            is InternalFuncStartAnnotation -> Annotation(
                INTERNAL_FUNC_START,
                fromCurrentRunTable.v.mergeAll(v, logger)
            )
            is SummaryStack.SummaryStart.External -> Annotation(
                START_EXTERNAL_SUMMARY,
                fromCurrentRunTable.v.mergeAll(v, logger)
            )
            is SummaryStack.SummaryStart.Internal -> Annotation(
                START_INTERNAL_SUMMARY,
                fromCurrentRunTable.v.mergeAll(v, logger)
            )
            is SnippetCmd -> Annotation(TACMeta.SNIPPET, fromCurrentRunTable.v.mergeAll(v, logger))
            else -> fromCurrentRunTable
        }
    }.warnIf(logger, { it == null && k.restore }) { "cannot patch $this and $fromCurrentRunTable" }


/**
 * The actual implementation of [Annotation.patch]
 * It can be assumed that [this] and [otherWithCanonical] are of the same concrete class with the same internal structure.
 * Where [this] is current-run meta-data that has information needed for generating a counter-example
 * And [otherWithCanonical] has [TACSymbol] and meta-ids
 *
 * This function use the interfaces [TransformableEntity], [TransformableSymAndVarEntity], [UniqueIdEntity]
 * for each exists a transform function map the class to itself
 * (note: this property is not guaranteed by the signature but assumed by us)
 *
 * So for each interface we call:
 * ```
 *      idents = mutableListOf()
 *      otherWithCanonical.transform { idents.add(it) ;it }
 *      this.transformSymbols { idents.removeFirst() }
 * ```
 * i.e. traverse [otherWithCanonical], and with the accumulated information transform [this]
 *
 * The result should return [this] with all the canonical identifiers replacing the current-run ones
 *
 * Note: if for some reason we fail to merge any of the interfaces, we return [otherWithCanonical]
 * So the counter-example will show stale-information
 **/
private inline fun <reified T> Any.mergeAll(otherWithCanonical: T, logger: Logger): T =
    (this as T).mergeSymbols(otherWithCanonical, logger).mergeVariables(otherWithCanonical, logger)
        .mergeIds(otherWithCanonical, logger)

private inline fun <reified T> T.mergeSymbols(other: T, logger: Logger): T = when {
    this is TransformableSymEntity<*> && other is TransformableSymEntity<*> -> this.merge(other, logger) as T
    this is TransformableVarEntity<*> && other is TransformableVarEntity<*> -> this.merge(other, logger) as T
    else -> this
}


/**
 * when taking symbols via [TransformableEntity.transformSymbols] keep the [MetaMap] from the [fromCurrentRunTable]
 **/
fun <S : TACSymbol> S.patchSymbol(fromCurrentRunTable: S, logger: Logger): S = when {
    this is TACSymbol.Var && fromCurrentRunTable is TACSymbol.Var -> {
        val patches = fromCurrentRunTable.meta.filter { (key, _) -> key.restore }
        withMeta { it.patch(patches, logger) }.uncheckedAs()
    }
    else -> this
}

private inline fun <S : TACSymbol, reified T : TransformableEntity<S, T>> T.merge(otherWithCanonical: T, logger: Logger): T {
    val syms = mutableListOf<S>()
    otherWithCanonical.transformSymbols { syms.add(it); it }

    var success = true
    val transformed = transformSymbols {
        val canonicalSym = syms.removeFirstOrNull()?.patchSymbol(it, logger)
        success = success && canonicalSym != null
        canonicalSym ?: it
    }
    if(!success) {
        logger.warn { "cannot merge symbols of $this with $otherWithCanonical" }
    }
    return transformed.takeIf { success } ?: otherWithCanonical
}

private inline fun <reified T> T.mergeVariables(otherWithCanonical: T, logger: Logger): T = when {
    this is TransformableSymAndVarEntity<*> && otherWithCanonical is TransformableSymAndVarEntity<*> -> {
        val vars = mutableListOf<TACSymbol.Var>()
        otherWithCanonical.transformVariables { vars.add(it); it }
        var success = true
        val transformed = transformVariables {
            val canonicalVar = vars.removeFirstOrNull()?.patchSymbol(it, logger)
            success = success && canonicalVar != null
            canonicalVar ?: it
        } as T
        if(!success) {
            logger.warn { "cannot merge variables of $this with $otherWithCanonical" }
        }
        transformed.takeIf { success } ?: otherWithCanonical
    }
    else -> this
}

private inline fun <reified T> T.mergeIds(otherWithCanonical: T, logger: Logger): T = when {
    this is UniqueIdEntity<*> && otherWithCanonical is UniqueIdEntity<*> -> {
        val ids = mutableListOf<Int>()
        otherWithCanonical.mapId { _, id, _ -> ids.add(id); id }
        var success = true
        val transformed = mapId { _, id, _ ->
            val canonicalId = ids.removeFirstOrNull()
            success = success && canonicalId != null
            canonicalId ?: id
        } as T
        if(!success) {
            logger.warn { "cannot merge ids of $this with $otherWithCanonical" }
        }
        transformed.takeIf { success } ?: otherWithCanonical
    }
    else -> this
}

private fun DisplayPath.structuralCheck(fromTable: DisplayPath): Boolean = when (this) {
    is DisplayPath.ArrayAccess -> fromTable is DisplayPath.ArrayAccess && base.structuralCheck(
        fromTable.base
    )
    is DisplayPath.FieldAccess -> fromTable is DisplayPath.FieldAccess && base.structuralCheck(
        fromTable.base
    )
    is DisplayPath.MapAccess -> fromTable is DisplayPath.MapAccess && base.structuralCheck(fromTable.base)
    is DisplayPath.Root -> fromTable is DisplayPath.Root
}
