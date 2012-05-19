sig Content {
	hash: Digest
}
sig Path {}
sig Digest {}

sig State {
	files: Path -> lone Content
}

sig History {
	change: State -> State
}

fact onlyOneHistory {
	all s1, s2: State, h: History | s2 in s1.^(h.change) or s1 in s2.^(h.change)
}

pred update (s, s': State, p: Path, c': Content) {
	all q: Path | p != q => s.files[q] = s'.files[q]
	s'.files[p] = c'
}

fact {
	all c1, c2: Content | c1 != c2 => c1.hash != c2.hash
}

fact {
	no h: History | all s, s': State | s' = s.(h.change) and s' = s
}

pred show {}

run show for 3 but 2 State

pred showUpdate (s, s': State, p: Path, c': Content) {
	s != s'
	s.files[p] != c'
	update [s, s', p, c']
}

pred showUpdate2 (s, s': State, p: Path, c': Content) {
	showUpdate [s, s', p, c']
	everyFileHasDifferentContent [s]
	everyFileHasDifferentContent [s']
	moreThanOneFile [s]
	moreThanOneFile [s']
}

pred everyFileHasDifferentContent (s: State) {
	all p1, p2: Path | p1 != p2 => s.files[p1] != s.files[p2]
}

pred moreThanOneFile (s: State) {
	#s.files > 2
}

run showUpdate2 for 4 but 1 History
