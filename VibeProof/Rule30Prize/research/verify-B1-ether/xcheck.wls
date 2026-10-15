cols = {"0011", "0110", "1101", "0101", "0011", "0001", "0001"};
tab = Transpose[Characters /@ cols] /. {"0" -> 0, "1" -> 1};  (* tab[[phase+1]] = row of 7 *)
row0 = Flatten[ConstantArray[tab[[1]], 5]];  (* cyclic row of length 35 *)
evo = CellularAutomaton[30, row0, 12];
expected = Table[Flatten[ConstantArray[tab[[Mod[t, 4] + 1]], 5]], {t, 0, 12}];
Print["CellularAutomaton[30] cyclic evolution equals ether table: ", evo === expected];
Print["rows: ", Row /@ tab];
