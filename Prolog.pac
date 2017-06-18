| package |
package := Package name: 'Prolog'.
package paxVersion: 1;
	basicComment: ''.


package classNames
	add: #C;
	add: #Pair;
	add: #Term;
	add: #V;
	yourself.

package binaryGlobalNames: (Set new
	yourself).

package globalAliases: (Set new
	yourself).

package setPrerequisites: (IdentitySet new
	add: 'Core\Object Arts\Dolphin\Base\Dolphin';
	yourself).

package!

"Class Definitions"!

Object subclass: #Term
	instanceVariableNames: ''
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Term subclass: #C
	instanceVariableNames: 'value'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Term subclass: #Pair
	instanceVariableNames: 'a b'
	classVariableNames: ''
	poolDictionaries: ''
	classInstanceVariableNames: ''!
Term subclass: #V
	instanceVariableNames: 'name undefined value'
	classVariableNames: 'Variables'
	poolDictionaries: ''
	classInstanceVariableNames: ''!

"Global Aliases"!


"Loose Methods"!

"End of package definition"!

"Source Globals"!

"Classes"!

Term guid: (GUID fromString: '{E8BA7277-9580-4EA2-8D18-C508A94AB599}')!
Term comment: ''!
!Term categoriesForClass!Kernel-Objects! !
!Term methodsFor!

% aValue
	^Pair a: self b: (C % aValue).!

, aTerm
	^Pair a: self b: aTerm!

@ aName
	^Pair a: self b: (V @ aName)!

go: aTerm do: aBlock
	(self unify: aTerm) ifTrue: [
		aBlock value. 
	self setUndefined.
	aTerm setUndefined.
]!

isC
	^false.!

isPair
	^false.!

isV
	^false.!

setUndefined
	^self subclassResponsibility!

unify: aTerm
	^self subclassResponsibility.
! !
!Term categoriesFor: #%!public! !
!Term categoriesFor: #,!public! !
!Term categoriesFor: #@!public! !
!Term categoriesFor: #go:do:!public! !
!Term categoriesFor: #isC!public! !
!Term categoriesFor: #isPair!public! !
!Term categoriesFor: #isV!public! !
!Term categoriesFor: #setUndefined!public! !
!Term categoriesFor: #unify:!public! !

C guid: (GUID fromString: '{DF2CB3DC-C88C-46E8-AAAC-E10B2B05983A}')!
C comment: ''!
!C categoriesForClass!Kernel-Objects! !
!C methodsFor!

= aValue
	^value = aValue!

initialize: aValue
	value:= aValue.!

isC
	^true.!

setUndefined!

unify: aTerm
	(aTerm isC)  ifTrue: [^(value = (aTerm value))].
	(aTerm isV)  ifTrue: [^aTerm unify: self].
	^false.
!

value
	^value.! !
!C categoriesFor: #=!public! !
!C categoriesFor: #initialize:!private! !
!C categoriesFor: #isC!public! !
!C categoriesFor: #setUndefined!public! !
!C categoriesFor: #unify:!public! !
!C categoriesFor: #value!public! !

!C class methodsFor!

% aValue
	 ^(self new) initialize: aValue;
        yourself.
! !
!C class categoriesFor: #%!public! !

Pair guid: (GUID fromString: '{A2BB9966-EC53-4408-8520-BFA895D8DE5B}')!
Pair comment: ''!
!Pair categoriesForClass!Kernel-Objects! !
!Pair methodsFor!

car
	^a.!

cdr
	^b.!

initializeA: aA B: aB
	a:=aA.
	b:=aB.
!

isPair
	^true.!

setUndefined
	a setUndefined.
	b setUndefined.!

unify: aTerm
	(aTerm isPair) 
		ifTrue: [Transcript show: 'unify pair, '.
			^((a unify: (aTerm car)) & (b unify: (aTerm cdr)))] 
		ifFalse: [(aTerm isV )
			ifTrue: [Transcript show: 'symetric pair->v, '.
			^aTerm unify: self] 
			ifFalse: [^false]
		].!

value
	^Pair a: (a value) b: (b value).! !
!Pair categoriesFor: #car!public! !
!Pair categoriesFor: #cdr!public! !
!Pair categoriesFor: #initializeA:B:!private! !
!Pair categoriesFor: #isPair!public! !
!Pair categoriesFor: #setUndefined!public! !
!Pair categoriesFor: #unify:!public! !
!Pair categoriesFor: #value!public! !

!Pair class methodsFor!

a: aA b: aB
	^(self new)
	initializeA: aA B: aB;
        yourself.
! !
!Pair class categoriesFor: #a:b:!public! !

V guid: (GUID fromString: '{DDABE01C-417F-4D54-B423-2AB741E67FC0}')!
V comment: ''!
!V categoriesForClass!Kernel-Objects! !
!V methodsFor!

= aTerm
	(aTerm isMemberOf: V)
		ifTrue: [^name = aTerm name.] 
		ifFalse: [^false.]
!

car
	^value car.!

cdr
	^value cdr.!

initialize: aName
	name := aName.
	value := nil.
	undefined := true.!

isV
	^true.!

name
	^name.!

setUndefined
	value := nil.
	undefined := true.
!

setValue: aValue
	value := aValue.
	undefined := false.
Transcript show: 'set varialbe '.
Transcript show: name.
!

unify: aTerm
	undefined 
		ifTrue: [ Transcript show: 'variable undefined, '.
			aTerm isC ifTrue: [self setValue: aTerm. 
					   ^true].
			aTerm isPair ifTrue: [((self = aTerm car) | (self = aTerm cdr)) 
							ifTrue: [^false] 
							ifFalse: [self setValue: aTerm. ^true.]
							].
			aTerm isV ifTrue: [(self = aTerm) 
							ifFalse: [self setValue: aTerm].
							^true
					          ].
		]
		ifFalse: [  Transcript show: 'variable defined, '.
		^value unify: aTerm].

!

value
	undefined 
		ifTrue: [ (Exception new messageText: 'Variable undefined') signal ] 
		ifFalse: [value isV ifTrue: [^value value] ifFalse: [^value]]! !
!V categoriesFor: #=!public! !
!V categoriesFor: #car!public! !
!V categoriesFor: #cdr!public! !
!V categoriesFor: #initialize:!public! !
!V categoriesFor: #isV!public! !
!V categoriesFor: #name!public! !
!V categoriesFor: #setUndefined!public! !
!V categoriesFor: #setValue:!public! !
!V categoriesFor: #unify:!public! !
!V categoriesFor: #value!public! !

!V class methodsFor!

@ aName
	| exists var | 
	exists := Variables includesKey: aName.
	exists 
		ifTrue: [^Variables at: aName] 
		ifFalse: [var := (self new) initialize: aName.
				Variables add: aName -> var.
				^var. 
				]!

initialize
	Variables := Dictionary new.! !
!V class categoriesFor: #@!public! !
!V class categoriesFor: #initialize!private! !

"Binary Globals"!

