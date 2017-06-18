V initialize.
t := L % 1, (V @ 2 % 3).
self assert: [t car car value isNil].
self assert: [t car cdr value = 1].
self assert: [t car value car isNil].
self assert: [t car value cdr = 1].
self assert: [t cdr cdr value = 3].

a := V @ 1.
b := V @ 2.
c := V @ 1.
self assert: [a ~= b].
self assert: [a == c].

t := C % 1 @ #z.
self assert: [t car value = 1].
w := 0.
[t value] on: Error do: [:ex | w := w + 1].
self assert: [w = 1].

C % 1 go: C % 2 do: [self assert: [false]].

w := 0.
C % 1 go: C % 1 do: [w := w + 1].
self assert: [w = 1].

x := V @ #x.
y := V @ #y.
w := 0.
x % 1 go: C % 2, y do:
    [w := w + 1.
    self assert: [x value = 2].
    self assert: [y value = 1]].
self assert: [w = 1].

w := 0.
C % 1 % 2 go: x do:
    [w := w + 1.
    self assert: [x value car = 1].
    self assert: [x cdr value = 2]].
self assert: [w = 1].

w := 0.
x go: C % $a do:
    [w := w + 1.
    x go: C % $b do: [self assert: [false]]].
x go: C % $b do: [w := w + 1].
self assert: [w = 2].

w := 0.
x % 1 go: y, y do:
    [w := w + 1.
    self assert: [x value = 1].
    self assert: [y value = 1]].
self assert: [w = 1].

x go: L, x do: [self assert: [false]].