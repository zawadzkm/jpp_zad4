|v1 v2 a b c |
V initialize.
c := C % 4.
v1 := V @ 1.
v2 := V @ (0 + 1).
Transcript show: '1'.
e := v1 == v2.
Transcript show: '2'.

Transcript show: (e class printString).

a := V @ 1.
b := V @ 2.
c := V @ 1.
self assert: [a ~= b].
self assert: [a == c].