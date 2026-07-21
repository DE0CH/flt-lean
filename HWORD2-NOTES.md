# hword2 telescope: normalized hypothesis and goal shapes
(compressed: K, W, SA/SB slopes, NA/NB intercepts, ROOTS_A/B/ln root multisets,
P.=Polynomial, M.=Multiset, ev=AdjoinRoot.evalEval; extracted from the goal state
at the hword2 sorry BEFORE the map_map extension — recheck λ-shapes after it)

## hwwN
hwwN : (M.map (fun i => (M.map (fun ab => i.2 - (ab.1 * i.1 + ab.2)) Ln).prod) (M.map (fun x => (x, SA * x + (NA))) (P.X ^ 3 + P.C (W.a₂ - SA ^ 2 - W.a₁ * SA) * P.X ^ 2 + P.C (W.a₄ - 2 * SA * (NA) - W.a₁ * (NA) - W.a₃ * SA) * P.X + P.C (W.a₆ - (NA) ^ 2 - W.a₃ * (NA))).roots)).prod * (M.map (fun i => (M.map (fun cv => i.1 - cv) Vn).prod) (M.map (fun x => (x, SA * x + (NA))) (P.X ^ 3 + P.C (W.a₂ - SA ^ 2 - W.a₁ * SA) * P.X ^ 2 + P.C (W.a₄ - 2 * SA * (NA) - W.a₁ * (NA) - W.a₃ * SA) * P.X + P.C (W.a₆ - (NA) ^ 2 - W.a₃ * (NA))).roots)).prod * ((M.map (fun i => (M.map (fun ab => i.2 - (ab.1 * i.1 + ab.2)) Ln).prod) (M.map (fun x => (x, SB * x + (W.negY xR₁ yR₁ - SB * xR₁))) (P.X ^ 3 + P.C (W.a₂ - SB ^ 2 - W.a₁ * SB) * P.X ^ 2 + P.C (W.a₄ - 2 * SB * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₁ * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₃ * SB) * P.X + P.C (W.a₆ - (W.negY xR₁ yR₁ - SB * xR₁) ^ 2 - W.a₃ * (W.negY xR₁ yR₁ - SB * xR₁))).roots)).prod * (M.map (fun i => (M.map (fun cv => i.1 - cv) Vn).prod) (M.map (fun x => (x, SB * x + (W.negY xR₁ yR₁ - SB * xR₁))) (P.X ^ 3 + P.C (W.a₂ - SB ^ 2 - W.a₁ * SB) * P.X ^ 2 + P.C (W.a₄ - 2 * SB * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₁ * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₃ * SB) * P.X + P.C (W.a₆ - (W.negY xR₁ yR₁ - SB * xR₁) ^ 2 - W.a₃ * (W.negY xR₁ yR₁ - SB * xR₁))).roots)).prod) = (M.map (fun i => i.2 - (SA * i.1 + (NA))) (Ln.bind fun ln => M.map (fun x => (x, ln.1 * x + ln.2)) ROOTS_ln).prod * (M.map (fun i => i.2 - (SB * i.1 + (W.negY xR₁ yR₁ - SB * xR₁))) (Ln.bind fun ln => M.map (fun x => (x, ln.1 * x + ln.2)) ROOTS_ln).prod * ((M.map (fun i => i.2 - (SA * i.1 + (NA))) (M.map (fun a => (a, W.negY a (yfib a))) Vn)).prod * (M.map (fun i => i.2 - (SB * i.1 + (W.negY xR₁ yR₁ - SB * xR₁))) (M.map (fun a => (a, W.negY a (yfib a))) Vn)).prod * ((M.map (fun i => i.2 - (SA * i.1 + (NA))) (M.map (fun x => (x, yfib x)) Vn)).prod * (M.map (fun i => i.2 - (SB * i.1 + (W.negY xR₁ yR₁ - SB * xR₁))) (M.map (fun x => (x, yfib x)) Vn)).prod))

## hwwNM
hwwNM : (M.map (fun x => W.negY xM (yfib xM) - (x.1 * xM + x.2)) Ln).prod * (M.map (fun x => xM - x) Vn).prod * ((M.map (fun x => yfib xM - (x.1 * xM + x.2)) Ln).prod * (M.map (fun x => xM - x) Vn).prod) = (-1) ^ (Ln.card * M.card 0) * ((M.map (fun x => x.1 - xM) (Ln.bind fun ln => M.map (fun x => (x, ln.1 * x + ln.2)) ROOTS_ln).prod * ((M.map (fun x => x.1 - xM) (M.map (fun a => (a, W.negY a (yfib a))) Vn)).prod * (M.map (fun x => x.1 - xM) (M.map (fun x => (x, yfib x)) Vn)).prod))

## hwwD
hwwD : (M.map (fun i => (M.map (fun ab => i.2 - (ab.1 * i.1 + ab.2)) Ld).prod) (M.map (fun x => (x, SA * x + (NA))) (P.X ^ 3 + P.C (W.a₂ - SA ^ 2 - W.a₁ * SA) * P.X ^ 2 + P.C (W.a₄ - 2 * SA * (NA) - W.a₁ * (NA) - W.a₃ * SA) * P.X + P.C (W.a₆ - (NA) ^ 2 - W.a₃ * (NA))).roots)).prod * (M.map (fun i => (M.map (fun cv => i.1 - cv) Vd).prod) (M.map (fun x => (x, SA * x + (NA))) (P.X ^ 3 + P.C (W.a₂ - SA ^ 2 - W.a₁ * SA) * P.X ^ 2 + P.C (W.a₄ - 2 * SA * (NA) - W.a₁ * (NA) - W.a₃ * SA) * P.X + P.C (W.a₆ - (NA) ^ 2 - W.a₃ * (NA))).roots)).prod * ((M.map (fun i => (M.map (fun ab => i.2 - (ab.1 * i.1 + ab.2)) Ld).prod) (M.map (fun x => (x, SB * x + (W.negY xR₁ yR₁ - SB * xR₁))) (P.X ^ 3 + P.C (W.a₂ - SB ^ 2 - W.a₁ * SB) * P.X ^ 2 + P.C (W.a₄ - 2 * SB * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₁ * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₃ * SB) * P.X + P.C (W.a₆ - (W.negY xR₁ yR₁ - SB * xR₁) ^ 2 - W.a₃ * (W.negY xR₁ yR₁ - SB * xR₁))).roots)).prod * (M.map (fun i => (M.map (fun cv => i.1 - cv) Vd).prod) (M.map (fun x => (x, SB * x + (W.negY xR₁ yR₁ - SB * xR₁))) (P.X ^ 3 + P.C (W.a₂ - SB ^ 2 - W.a₁ * SB) * P.X ^ 2 + P.C (W.a₄ - 2 * SB * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₁ * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₃ * SB) * P.X + P.C (W.a₆ - (W.negY xR₁ yR₁ - SB * xR₁) ^ 2 - W.a₃ * (W.negY xR₁ yR₁ - SB * xR₁))).roots)).prod) = (M.map (fun i => i.2 - (SA * i.1 + (NA))) (Ld.bind fun ln => M.map (fun x => (x, ln.1 * x + ln.2)) ROOTS_ln).prod * (M.map (fun i => i.2 - (SB * i.1 + (W.negY xR₁ yR₁ - SB * xR₁))) (Ld.bind fun ln => M.map (fun x => (x, ln.1 * x + ln.2)) ROOTS_ln).prod * ((M.map (fun i => i.2 - (SA * i.1 + (NA))) (M.map (fun a => (a, W.negY a (yfib a))) Vd)).prod * (M.map (fun i => i.2 - (SB * i.1 + (W.negY xR₁ yR₁ - SB * xR₁))) (M.map (fun a => (a, W.negY a (yfib a))) Vd)).prod * ((M.map (fun i => i.2 - (SA * i.1 + (NA))) (M.map (fun x => (x, yfib x)) Vd)).prod * (M.map (fun i => i.2 - (SB * i.1 + (W.negY xR₁ yR₁ - SB * xR₁))) (M.map (fun x => (x, yfib x)) Vd)).prod))

## hwwDM
hwwDM : (M.map (fun x => W.negY xM (yfib xM) - (x.1 * xM + x.2)) Ld).prod * (M.map (fun x => xM - x) Vd).prod * ((M.map (fun x => yfib xM - (x.1 * xM + x.2)) Ld).prod * (M.map (fun x => xM - x) Vd).prod) = (-1) ^ (Ld.card * M.card 0) * ((M.map (fun x => x.1 - xM) (Ld.bind fun ln => M.map (fun x => (x, ln.1 * x + ln.2)) ROOTS_ln).prod * ((M.map (fun x => x.1 - xM) (M.map (fun a => (a, W.negY a (yfib a))) Vd)).prod * (M.map (fun x => x.1 - xM) (M.map (fun x => (x, yfib x)) Vd)).prod))

## hcvtN
hcvtN : (M.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ln).prod * (M.map (fun x => xQR₁ - x) Vn).prod * ((M.map (fun x => W.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ln).prod * (M.map (fun x => xR₁ - x) Vn).prod * ((M.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ln).prod * (M.map (fun x => xR₃ - x) Vn).prod * ((M.map (fun x => W.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ln).prod * (M.map (fun x => xQR₃ - x) Vn).prod))) * ((M.map (fun x => W.negY xM (yfib xM) - (x.1 * xM + x.2)) Ln).prod * (M.map (fun x => xM - x) Vn).prod * ((M.map (fun x => yfib xM - (x.1 * xM + x.2)) Ln).prod * (M.map (fun x => xM - x) Vn).prod)) = (M.map (fun i => (M.map (fun ab => i.2 - (ab.1 * i.1 + ab.2)) Ln).prod) (M.map (fun x => (x, SA * x + (NA))) (P.X ^ 3 + P.C (W.a₂ - SA ^ 2 - W.a₁ * SA) * P.X ^ 2 + P.C (W.a₄ - 2 * SA * (NA) - W.a₁ * (NA) - W.a₃ * SA) * P.X + P.C (W.a₆ - (NA) ^ 2 - W.a₃ * (NA))).roots)).prod * (M.map (fun i => (M.map (fun cv => i.1 - cv) Vn).prod) (M.map (fun x => (x, SA * x + (NA))) (P.X ^ 3 + P.C (W.a₂ - SA ^ 2 - W.a₁ * SA) * P.X ^ 2 + P.C (W.a₄ - 2 * SA * (NA) - W.a₁ * (NA) - W.a₃ * SA) * P.X + P.C (W.a₆ - (NA) ^ 2 - W.a₃ * (NA))).roots)).prod * ((M.map (fun i => (M.map (fun ab => i.2 - (ab.1 * i.1 + ab.2)) Ln).prod) (M.map (fun x => (x, SB * x + (W.negY xR₁ yR₁ - SB * xR₁))) (P.X ^ 3 + P.C (W.a₂ - SB ^ 2 - W.a₁ * SB) * P.X ^ 2 + P.C (W.a₄ - 2 * SB * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₁ * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₃ * SB) * P.X + P.C (W.a₆ - (W.negY xR₁ yR₁ - SB * xR₁) ^ 2 - W.a₃ * (W.negY xR₁ yR₁ - SB * xR₁))).roots)).prod * (M.map (fun i => (M.map (fun cv => i.1 - cv) Vn).prod) (M.map (fun x => (x, SB * x + (W.negY xR₁ yR₁ - SB * xR₁))) (P.X ^ 3 + P.C (W.a₂ - SB ^ 2 - W.a₁ * SB) * P.X ^ 2 + P.C (W.a₄ - 2 * SB * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₁ * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₃ * SB) * P.X + P.C (W.a₆ - (W.negY xR₁ yR₁ - SB * xR₁) ^ 2 - W.a₃ * (W.negY xR₁ yR₁ - SB * xR₁))).roots)).prod)

## hcvtD
hcvtD : (M.map (fun x => yQR₁ - (x.1 * xQR₁ + x.2)) Ld).prod * (M.map (fun x => xQR₁ - x) Vd).prod * ((M.map (fun x => W.negY xR₁ yR₁ - (x.1 * xR₁ + x.2)) Ld).prod * (M.map (fun x => xR₁ - x) Vd).prod * ((M.map (fun x => yR₃ - (x.1 * xR₃ + x.2)) Ld).prod * (M.map (fun x => xR₃ - x) Vd).prod * ((M.map (fun x => W.negY xQR₃ yQR₃ - (x.1 * xQR₃ + x.2)) Ld).prod * (M.map (fun x => xQR₃ - x) Vd).prod))) * ((M.map (fun x => W.negY xM (yfib xM) - (x.1 * xM + x.2)) Ld).prod * (M.map (fun x => xM - x) Vd).prod * ((M.map (fun x => yfib xM - (x.1 * xM + x.2)) Ld).prod * (M.map (fun x => xM - x) Vd).prod)) = (M.map (fun i => (M.map (fun ab => i.2 - (ab.1 * i.1 + ab.2)) Ld).prod) (M.map (fun x => (x, SA * x + (NA))) (P.X ^ 3 + P.C (W.a₂ - SA ^ 2 - W.a₁ * SA) * P.X ^ 2 + P.C (W.a₄ - 2 * SA * (NA) - W.a₁ * (NA) - W.a₃ * SA) * P.X + P.C (W.a₆ - (NA) ^ 2 - W.a₃ * (NA))).roots)).prod * (M.map (fun i => (M.map (fun cv => i.1 - cv) Vd).prod) (M.map (fun x => (x, SA * x + (NA))) (P.X ^ 3 + P.C (W.a₂ - SA ^ 2 - W.a₁ * SA) * P.X ^ 2 + P.C (W.a₄ - 2 * SA * (NA) - W.a₁ * (NA) - W.a₃ * SA) * P.X + P.C (W.a₆ - (NA) ^ 2 - W.a₃ * (NA))).roots)).prod * ((M.map (fun i => (M.map (fun ab => i.2 - (ab.1 * i.1 + ab.2)) Ld).prod) (M.map (fun x => (x, SB * x + (W.negY xR₁ yR₁ - SB * xR₁))) (P.X ^ 3 + P.C (W.a₂ - SB ^ 2 - W.a₁ * SB) * P.X ^ 2 + P.C (W.a₄ - 2 * SB * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₁ * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₃ * SB) * P.X + P.C (W.a₆ - (W.negY xR₁ yR₁ - SB * xR₁) ^ 2 - W.a₃ * (W.negY xR₁ yR₁ - SB * xR₁))).roots)).prod * (M.map (fun i => (M.map (fun cv => i.1 - cv) Vd).prod) (M.map (fun x => (x, SB * x + (W.negY xR₁ yR₁ - SB * xR₁))) (P.X ^ 3 + P.C (W.a₂ - SB ^ 2 - W.a₁ * SB) * P.X ^ 2 + P.C (W.a₄ - 2 * SB * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₁ * (W.negY xR₁ yR₁ - SB * xR₁) - W.a₃ * SB) * P.X + P.C (W.a₆ - (W.negY xR₁ yR₁ - SB * xR₁) ^ 2 - W.a₃ * (W.negY xR₁ yR₁ - SB * xR₁))).roots)).prod)

## hpjA
hpjA : (yPS₁ - (SA * xPS₁ + (NA))) ^ p * (W.negY xS₁ yS₁ - (SA * xS₁ + (NA))) ^ p * ((M.map (fun x => x.2 - (SA * x.1 + (NA))) (Ld.bind fun ln => M.map (fun x => (x, ln.1 * x + ln.2)) ROOTS_ln).prod * ((M.map (fun x => x.2 - (SA * x.1 + (NA))) (M.map (fun a => (a, W.negY a (yfib a))) Vd)).prod * (M.map (fun x => x.2 - (SA * x.1 + (NA))) (M.map (fun x => (x, yfib x)) Vd)).prod)) = (M.map (fun x => x.2 - (SA * x.1 + (NA))) (Ln.bind fun ln => M.map (fun x => (x, ln.1 * x + ln.2)) ROOTS_ln).prod * ((M.map (fun x => x.2 - (SA * x.1 + (NA))) (M.map (fun a => (a, W.negY a (yfib a))) Vn)).prod * (M.map (fun x => x.2 - (SA * x.1 + (NA))) (M.map (fun x => (x, yfib x)) Vn)).prod)

## hpjB
hpjB : (yPS₁ - (SB * xPS₁ + (W.negY xR₁ yR₁ - SB * xR₁))) ^ p * (W.negY xS₁ yS₁ - (SB * xS₁ + (W.negY xR₁ yR₁ - SB * xR₁))) ^ p * ((M.map (fun x => x.2 - (SB * x.1 + (W.negY xR₁ yR₁ - SB * xR₁))) (Ld.bind fun ln => M.map (fun x => (x, ln.1 * x + ln.2)) ROOTS_ln).prod * ((M.map (fun x => x.2 - (SB * x.1 + (W.negY xR₁ yR₁ - SB * xR₁))) (M.map (fun a => (a, W.negY a (yfib a))) Vd)).prod * (M.map (fun x => x.2 - (SB * x.1 + (W.negY xR₁ yR₁ - SB * xR₁))) (M.map (fun x => (x, yfib x)) Vd)).prod)) = (M.map (fun x => x.2 - (SB * x.1 + (W.negY xR₁ yR₁ - SB * xR₁))) (Ln.bind fun ln => M.map (fun x => (x, ln.1 * x + ln.2)) ROOTS_ln).prod * ((M.map (fun x => x.2 - (SB * x.1 + (W.negY xR₁ yR₁ - SB * xR₁))) (M.map (fun a => (a, W.negY a (yfib a))) Vn)).prod * (M.map (fun x => x.2 - (SB * x.1 + (W.negY xR₁ yR₁ - SB * xR₁))) (M.map (fun x => (x, yfib x)) Vn)).prod)

## hpjM
hpjM : (xPS₁ - xM) ^ p * (xS₁ - xM) ^ p * ((M.map (fun x => x.1 - xM) (Ld.bind fun ln => M.map (fun x => (x, ln.1 * x + ln.2)) ROOTS_ln).prod * ((M.map (fun x => x.1 - xM) (M.map (fun a => (a, W.negY a (yfib a))) Vd)).prod * (M.map (fun x => x.1 - xM) (M.map (fun x => (x, yfib x)) Vd)).prod)) = (M.map (fun x => x.1 - xM) (Ln.bind fun ln => M.map (fun x => (x, ln.1 * x + ln.2)) ROOTS_ln).prod * ((M.map (fun x => x.1 - xM) (M.map (fun a => (a, W.negY a (yfib a))) Vn)).prod * (M.map (fun x => x.1 - xM) (M.map (fun x => (x, yfib x)) Vn)).prod) ⊢ uf * ((M.map (fun ln => yQR₁ - (ln.1 * xQR₁ + ln.2)) Ln).prod * (M.map (fun c => xQR₁ - c) Vn).prod) * (uf * ((M.map (fun ln => W.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2)) Ln).prod * (M.map (fun c => xR₁ - c) Vn).prod)) * (uf * ((M.map (fun ln => yR₃ - (ln.1 * xR₃ + ln.2)) Ln).prod * (M.map (fun c => xR₃ - c) Vn).prod)) * (uf * ((M.map (fun ln => W.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2)) Ln).prod * (M.map (fun c => xQR₃ - c) Vn).prod)) * ((xR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xQR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * (c * ((yS₁ - (SA * xS₁ + (NA))) * (yS₁ - (SB * xS₁ + (W.negY xR₁ yR₁ - SB * xR₁)))) * (c * ((W.negY xS₁ yS₁ - (SA * xS₁ + (NA))) * (W.negY xS₁ yS₁ - (SB * xS₁ + (W.negY xR₁ yR₁ - SB * xR₁)))))) ^ p * ((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p * ((xPS₁ - xM) * (xS₁ - xM)) ^ p * ((M.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod * (M.map (fun c => xR₁ - c) Vd).prod) * ((M.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod * (M.map (fun c => xQR₃ - c) Vd).prod) = uf * ((M.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ln).prod * (M.map (fun c => xR₁ - c) Vn).prod) * (uf * ((M.map (fun ln => W.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2)) Ln).prod * (M.map (fun c => xR₁ - c) Vn).prod)) * (uf * ((M.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ln).prod * (M.map (fun c => xQR₃ - c) Vn).prod)) * (uf * ((M.map (fun ln => W.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2)) Ln).prod * (M.map (fun c => xQR₃ - c) Vn).prod)) * ((xQR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * (c * ((yPS₁ - (SA * xPS₁ + (NA))) * (yPS₁ - (SB * xPS₁ + (W.negY xR₁ yR₁ - SB * xR₁)))) * (c * ((W.negY xS₁ yS₁ - (SA * xS₁ + (NA))) * (W.negY xS₁ yS₁ - (SB * xS₁ + (W.negY xR₁ yR₁ - SB * xR₁)))))) ^ p * ((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p * ((xS₁ - xM) * (xS₁ - xM)) ^ p * ((M.map (fun ln => yQR₁ - (ln.1 * xQR₁ + ln.2)) Ld).prod * (M.map (fun c => xQR₁ - c) Vd).prod) * ((M.map (fun ln => yR₃ - (ln.1 * xR₃ + ln.2)) Ld).prod * (M.map (fun c => xR₃ - c) Vd).prod)

## GOAL
⊢ uf * ((M.map (fun ln => yQR₁ - (ln.1 * xQR₁ + ln.2)) Ln).prod * (M.map (fun c => xQR₁ - c) Vn).prod) * (uf * ((M.map (fun ln => W.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2)) Ln).prod * (M.map (fun c => xR₁ - c) Vn).prod)) * (uf * ((M.map (fun ln => yR₃ - (ln.1 * xR₃ + ln.2)) Ln).prod * (M.map (fun c => xR₃ - c) Vn).prod)) * (uf * ((M.map (fun ln => W.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2)) Ln).prod * (M.map (fun c => xQR₃ - c) Vn).prod)) * ((xR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xQR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * (c * ((yS₁ - (SA * xS₁ + (NA))) * (yS₁ - (SB * xS₁ + (W.negY xR₁ yR₁ - SB * xR₁)))) * (c * ((W.negY xS₁ yS₁ - (SA * xS₁ + (NA))) * (W.negY xS₁ yS₁ - (SB * xS₁ + (W.negY xR₁ yR₁ - SB * xR₁)))))) ^ p * ((xPS₁ - xR₁) * (xPS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p * ((xPS₁ - xM) * (xS₁ - xM)) ^ p * ((M.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ld).prod * (M.map (fun c => xR₁ - c) Vd).prod) * ((M.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ld).prod * (M.map (fun c => xQR₃ - c) Vd).prod) = uf * ((M.map (fun ln => yR₁ - (ln.1 * xR₁ + ln.2)) Ln).prod * (M.map (fun c => xR₁ - c) Vn).prod) * (uf * ((M.map (fun ln => W.negY xR₁ yR₁ - (ln.1 * xR₁ + ln.2)) Ln).prod * (M.map (fun c => xR₁ - c) Vn).prod)) * (uf * ((M.map (fun ln => yQR₃ - (ln.1 * xQR₃ + ln.2)) Ln).prod * (M.map (fun c => xQR₃ - c) Vn).prod)) * (uf * ((M.map (fun ln => W.negY xQR₃ yQR₃ - (ln.1 * xQR₃ + ln.2)) Ln).prod * (M.map (fun c => xQR₃ - c) Vn).prod)) * ((xQR₁ - xS₁) ^ p * (xR₁ - xS₁) ^ p * (xR₃ - xS₁) ^ p * (xQR₃ - xS₁) ^ p) * (c * ((yPS₁ - (SA * xPS₁ + (NA))) * (yPS₁ - (SB * xPS₁ + (W.negY xR₁ yR₁ - SB * xR₁)))) * (c * ((W.negY xS₁ yS₁ - (SA * xS₁ + (NA))) * (W.negY xS₁ yS₁ - (SB * xS₁ + (W.negY xR₁ yR₁ - SB * xR₁)))))) ^ p * ((xS₁ - xR₁) * (xS₁ - xQR₃) * ((xS₁ - xR₁) * (xS₁ - xQR₃))) ^ p * ((xS₁ - xM) * (xS₁ - xM)) ^ p * ((M.map (fun ln => yQR₁ - (ln.1 * xQR₁ + ln.2)) Ld).prod * (M.map (fun c => xQR₁ - c) Vd).prod) * ((M.map (fun ln => yR₃ - (ln.1 * xR₃ + ln.2)) Ld).prod * (M.map (fun c => xR₃ - c) Vd).prod)

## Atom-closure map (derived 2026-07-21, second pass)

The goal's word-value atoms at the six setup points close as follows:
- P1..P4 (the Dt points): through hcvtN/hcvtD (LHS gives PhiN/PhiD at
  P1..P4 times the two xM-fiber values; RHS = the per-chord ROOTS_A/B
  products) chained with hwwN/hwwD (per-chord products = LnA*LnB*VnfA*VnfB
  resp. Ld-versions) and hpjA/hpjB (DP-values times Ld-side = Ln-side).
- P5, P6 (the sigma-companions (xR1,yR1), (xQR3,yQR3)): through the OUTER
  instances hwv7 (= hww Ln 0 Vn {xR1,xQR3}) and hwv8 (= hww Ld 0 Vd
  {xR1,xQR3}): PhiN(P2)PhiN(P5)PhiN(P4)PhiN(P6) = prod over
  can(Ln)+fib(Vn) of (x-xR1)(x-xQR3), and the D-version. The P2/P4
  factors also occur in the P1..P4 chain, so they cancel between the two
  chains in the telescope.
- The W-groups ((xPS1-xR1)(xPS1-xQR3)... ^p) and V-groups pair with
  hpjM-analogues at (x-xR1),(x-xQR3): NOT bound — instead hwv3/hwv4
  (= hww 0 Ln {xR1,xQR3} Vn / Ld-version) give prod over can+fib of
  (x-xR1)(x-xQR3) — the same RHS atoms as hwv7/hwv8's LHS — and their
  fiber sides are the explicit S1-fiber... CORRECTION: hwv3/4's RHS is
  over fib({xR1,xQR3}) = PhiN at P2,P5,P4,P6 — same as hwv7/8. The
  DP-side (x-xR1)(x-xQR3) values (the W-groups, at PS1 and -S1, ^p)
  connect via hcvP at (fun T => T.1 - xR1) and (fun T => T.1 - xQR3):
  TWO MORE PROJECTIONS TO BIND (safe: xR1, xQR3 differ from xS1, xPS1
  in F'-membership, no zero trap).
- ZERO TRAP: do NOT bind hcvP at (x - xS1) — its DP-side contains
  (xS1 - xS1)^p = 0. The V-group reconciliation must come through the
  (x - xR1)/(x - xQR3) projections and hwv9 (explicit fiber identity),
  never through an (x - xS1) projection.
- M-fiber junk (PhiN/PhiD at Mf+-): related to Lnm/Vnfm/Ldm/Vdfm by
  hwwNM/hwwDM and to the (xPS1-xM)^p(xS1-xM)^p factors by hpjM; all
  fiber values nonzero by the hDne argument (xM notin F'), needed for
  the final mul_right_cancel0.
- uf^4 appears on both goal sides and cancels; the c-powers live inside
  the T-groups and match the hpjA/hpjB DP-values raised to p exactly as
  in hword1's derivation.

NEXT: bind hcvP at (x - xR1) and (x - xQR3), then assemble the
telescoped linear_combination; multiply-cancel the M-fiber junk last.

## THE TELESCOPE, fully derived (2026-07-21, third pass)

Write Phi_N(i)/Phi_D(i) for the aP1 numerator/denominator word values at
point Pi (P1..P4 = the Dt points, P5/P6 the sigma-companions of P2/P4),
m/m' for Phi_N/Phi_D at the two xM-fiber points, TLam :=
LamA(PS1)^p LamA(-S1)^p LamB(PS1)^p LamB(-S1)^p, ZM/ZR/ZQ the
(xPS1-x*)^p (xS1-x*)^p pairs for xM/xR1/xQR3.

(i)  hcvtN + hwwN:  Phi_N(1)..Phi_N(4) * m = LnA LnB VnfA VnfB =: Y
(ii) hcvtD + hwwD:  Phi_D(1)..Phi_D(4) * m' = Y'
(iii) hpjA + hpjB:  Y = TLam * Y'   =>  Phi_N(1234) m = TLam Phi_D(1234) m'
(iv) hwwNM + hwwDM + hpjM:  m = ZM * m'
(v)  hwv7 + hwv8 + hpjR + hpjQ:  Phi_N(2546) = ZR ZQ Phi_D(2546)

Multiply the GOAL by (ZM * m'); substitute (iii)+(iv) on the left and
(v) on the right. Both sides then carry the SAME factor
Phi_D(1)...Phi_D(6) * m', leaving the explicit-scalar residue
   restL * TLam  vs  restR * ZR ZQ ZM,
whose mismatch is exactly [LamA(S1)LamB(S1)LamA(-S1)LamB(-S1)]^p.
This closes by the SIGMA-NORM identities (pure consequences of the
curve equation at S1 via equation_iff):
   LamA(S1)*LamA(-S1) = -cubicA(xS1)  (up to sign convention)
   LamB(S1)*LamB(-S1) = -cubicB(xS1)
where cubicA(xS1) = (xS1-xQR1)(xS1-xR3)(xS1-xM)-monic-cubic VALUE (as a
polynomial identity in the coordinates — do NOT use hbalt for this, just
expand: (y-l)(negY-l) with negY = -y - a1 x - a3 and the curve equation
eliminates y^2). Raised to p these supply exactly the leftover
(xS1-xM)^{2p}, V2's (xQR1-xS1)^p (xR3-xS1)^p, and W2/ZR/ZQ's
(xS1-xR1)^p (xS1-xQR3)^p factors. Sign bookkeeping: (a-b)^p vs (b-a)^p
pairs need hm1 : (-1:K)^p * (-1:K)^p = 1 (by <- mul_pow; norm_num) as a
combination input; count the pairs to place hm1's coefficient.

FINAL SHAPE of hword2's closure:
  have hnormA : LamA(S1)*LamA(-S1) = <explicit cubic value at xS1> := by
    linear_combination <coeff> * ((equation_iff xS1 yS1).mp hS1.left)
  have hnormB : ... (same with chord B)
  have hm1 : ((-1:K))^p * ((-1:K))^p = 1 := by rw [<- mul_pow]; norm_num
  have hmfne : m' (both Phi_D Mf-values) ≠ 0  -- hDne-style, xM notin F'
  refine mul_right_cancel₀ (mul_ne_zero ... hDne-factors 1..6 ... hmfne) ?_
  linear_combination (telescope coefficients as derived above — partial
    products along the two substitution chains, congrArg (·^p) on
    hnormA/hnormB for the powered norm identities)

NOTE: hDne (in scope from hword1!) already certifies Phi_D at P1..P6
nonzero — reuse it for the common-factor cancellation; only the two
Mf-values need a new nonzero argument.

## Residue closure WITHOUT Vieta (fourth pass — supersedes the hnorm route)

The scalar residue restL*TLam = restR*ZR*ZQ*ZM closes explicitly:
- hww Lnt 0 0 {xS1}: [Lam-values at the xS1-fiber pair] = prod over
  can(Lnt) of (x - xS1)  (sign (-1)^0 = 1); transport the canonical
  fiber pair to (yS1, negY yS1) by hfibpair xS1 yS1.
- hcvt (fun T => T.1 - xS1): prod over Dt+Mfib of (x - xS1) = prod over
  can(Lnt) of (x - xS1) — so [LamLamLamLam at S1-fiber] =
  (xQR1-xS1)(xR1-xS1)(xR3-xS1)(xQR3-xS1)(xM-xS1)^2, ALL EXPLICIT.
- Same pair with {xPS1} for the PS1-flavored Lambda values in TLam/T2.
- The V/W/Z-group reconciliation is then pure ring over these explicit
  products (raised to p after mul_pow splitting; signs pair as
  (a-b)^p(b-a)^p handled by hm1-type inputs or exponent-pairing).
The hnormA/hnormB coefficient-form identities (committed, proven) are
NOT needed on this route — retain them as backup.
Chains verified syntactically (string-normalized): hcvtN.R == hwwN.L,
hcvtD.R == hwwD.L, hwwNM.R == hpjM.R, hwwDM.R ⊂ hpjM.L — so
hN := hcvtN.trans hwwN and hD := hcvtD.trans hwwD are exact.
Raw post-simp hypothesis texts saved at scratchpad hword2-hyps.json.
J (cancel factor) := hDne-subject * hwwNM.LHS (the Phi_N M-fiber pair);
needs the N-version of hmfne (Ln/Vn, Or.inl memberships) — TO BIND.
