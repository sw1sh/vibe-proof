(* Independent check of the actual-pattern witnesses using CellularAutomaton *)
data = CellularAutomaton[30, {{1}, 0}, {{0, 20000}, {0, 2}}];
Print[Dimensions[data]];
c = data[[All, 1]]; b = data[[All, 2]]; e = data[[All, 3]];
Print[StringJoin[ToString /@ c[[1 ;; 20]]]];
(* t index: data[[t+1]] is time t *)
viol9 = Select[Range[0, 20000 - 9], AllTrue[c[[# + 1 ;; # + 9]], # == 1 &] && {b[[# + 10]], e[[# + 10]]} =!= {0, 1} &];
Print["violations of 9-absorption: ", viol9];
wit8 = Select[Range[0, 20000 - 8], AllTrue[c[[# + 1 ;; # + 8]], # == 1 &] && {b[[# + 9]], e[[# + 9]]} =!= {0, 1} &];
Print["8-step actual witnesses: ", wit8];
Print[Table[{t0, c[[t0 + 1 ;; t0 + 9]], {b[[t0 + 9]], e[[t0 + 9]]}}, {t0, wit8}]];
