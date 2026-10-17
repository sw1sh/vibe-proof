Needs["WolframInstitute`GAPLink`"];
session = StartGAPSession[];
Print["GAP ", session["Version"]];
phi[x_, n_] := Mod[BitXor[x, BitOr[2 x, 4 x]], 2^n];
sig[x_] := BitXor[x, 1];
tau[x_] := If[EvenQ[x], BitXor[x, 3], BitXor[x, 1]];
plist[f_, n_] := "[" <> StringRiffle[ToString /@ Table[f[x] + 1, {x, 0, 2^n - 1}], ","] <> "]";
gap[code_] := GAPEvaluate[session, code];
(* level quotients G_n = <Phi, sigma, tau> on 2^n points *)
Do[
  gap["P := PermList(" <> plist[phi[#, n] &, n] <> ");; S := PermList(" <> plist[sig, n] <>
    ");; T := PermList(" <> plist[If[n == 1, sig[#], tau[#]] &, n] <> ");;"];
  gap["G := Group(P, S, T);; N := NormalClosure(G, Group(S, T));;"];
  Print["n=", n, "  log2|G_n| = ", gap["Log(Size(G), 2);"],
    "  log2|N_n| = ", gap["Log(Size(N), 2);"], "  [G_n:N_n] = ", gap["Index(G, N);"],
    "  order(P) = ", gap["Order(P);"], "  AbInv(G_n) = ", gap["AbelianInvariants(G);"]],
  {n, 1, 8}];
(* the finitary filtration M_j on level D = 2j + 2 *)
Do[
  With[{D = 2 j + 2},
    gap["P := PermList(" <> plist[phi[#, D] &, D] <> ");; S := PermList(" <> plist[sig, D] <>
      ");; T := PermList(" <> plist[tau, D] <> ");;"];
    gap["M := Group(Concatenation(List([0.." <> ToString[j] <> "], i -> [P^-i*S*P^i, P^-i*T*P^i])));;"];
    Print["j=", j, " D=", D, "  log2|M_j| = ", gap["Log(Size(M), 2);"],
      "  log2|Aut(T_D)| = ", 2^D - 1, "  AbInv(M_j) = ", gap["AbelianInvariants(M);"],
      "  nilpotency class = ", gap["NilpotencyClassOfGroup(M);"]]],
  {j, 0, 3}];
DeleteObject[session];
