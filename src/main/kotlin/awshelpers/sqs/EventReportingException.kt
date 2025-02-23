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

package awshelpers.sqs

import aws.sdk.kotlin.runtime.auth.credentials.CredentialsProviderException
import aws.sdk.kotlin.services.sqs.model.SqsException
import kotlinx.coroutines.TimeoutCancellationException
import utils.CertoraErrorType
import utils.CertoraException

sealed class EventReportingException(message: String, cause: Throwable?) : CertoraException(CertoraErrorType.EVENT_REPORTING, message, cause) {
    class NoCredentials(cause: CredentialsProviderException) :
        EventReportingException("AWS credentials could not be loaded", cause)

    class InvalidToken(cause: SqsException) :
        EventReportingException("Invalid AWS client token", cause)

    class ExpiredToken(cause: SqsException) :
        EventReportingException("AWS security token has expired", cause)

    class AccessDenied(cause: SqsException) :
        EventReportingException("AWS account does not have sufficient privileges to execute request", cause)

    class Timeout(cause: TimeoutCancellationException) :
        EventReportingException("Request timed out", cause)

    class Other(cause: Throwable) :
        EventReportingException(cause.message ?: defaultMessage, cause)

    companion object {
        /** wraps an exception thrown from an event reporting context with a more specific [EventReportingException] */
        fun wrap(e: Throwable) =
            when {
                e is EventReportingException -> e
                e is CredentialsProviderException -> NoCredentials(e)
                e is TimeoutCancellationException -> Timeout(e)
                e is SqsException && e.sdkErrorMetadata.errorCode == "InvalidClientTokenId" -> InvalidToken(e)
                e is SqsException && e.sdkErrorMetadata.errorCode == "ExpiredToken" -> ExpiredToken(e)
                e is SqsException && e.sdkErrorMetadata.errorCode == "AccessDenied" -> AccessDenied(e)
                else -> Other(e)
            }
    }
}

private const val defaultMessage = "Unspecified failure occurred during event reporting"
