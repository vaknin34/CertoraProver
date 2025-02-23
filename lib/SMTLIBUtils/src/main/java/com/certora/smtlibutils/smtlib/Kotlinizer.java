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

package com.certora.smtlibutils.smtlib;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class Kotlinizer {
    public static <U extends Kotlinizable<T>,T> List<T> kotlinizeList(List<U> l)
    {
        Stream<T> a = l.stream().map(Kotlinizable::kotlinize);
        List<T> b = a.collect(Collectors.toList());
        return b;
    }
}
