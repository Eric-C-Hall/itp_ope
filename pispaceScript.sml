open HolKernel Parse boolLib bossLib;
open simpLib;
open markerTheory;
open combinTheory;
open pairTheory;
open pred_setTheory;
open arithmeticTheory;
open realTheory;
open realLib;
open limTheory;
open seqTheory;
open transcTheory;
open real_sigmaTheory;
open extrealTheory;
open sigma_algebraTheory;
open measureTheory;
open borelTheory;
open lebesgueTheory;
open martingaleTheory;
open probabilityTheory;
open trivialTheory;
open trivialSimps;

val _ = new_theory "pispace";

val _ = reveal "C";

val _ = augment_srw_ss [TRIVIAL_ss];

val name_to_thname = fn s => ({Thy = "pispace", Name = s}, DB.fetch "pispace" s);

(*
val _ = reveal "C";

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss];
*)

(*
val pi_pair_def = Define `pi_pair (n:num) f e = (λi. if (i = n) then e else f i)`;

val pi_cross_def = Define `pi_cross (n:num) fs s = {pi_pair n f e | f ∈ fs ∧ e ∈ s}`;

val pi_prod_sets_def = Define `pi_prod_sets n fsts sts = {pi_cross n fs s | fs ∈ fsts ∧ s ∈ sts}`;

val pi_m_space_def = Define `(pi_m_space 0 mss = {(λi. ARB)}) ∧
    (pi_m_space (SUC n) mss = pi_cross n (pi_m_space n mss) (m_space (mss n)))`;

val pi_measurable_sets_def = Define `(pi_measurable_sets 0 mss = POW {(λi. ARB)}) ∧
    (pi_measurable_sets (SUC n) mss = subsets (sigma (pi_m_space (SUC n) mss)
    (pi_prod_sets n (pi_measurable_sets n mss) (measurable_sets (mss n)))))`;

val pi_measure_def = Define `(pi_measure 0 mss = (λfs. if (fs = ∅) then 0 else 1)) ∧
    (pi_measure (SUC n) mss = (λfs. real (integral (mss n)
    (λe. Normal (pi_measure n mss ((PREIMAGE (λf. pi_pair n f e) fs) ∩ (pi_m_space n mss)))))))`;

val pi_measure_space_def = Define `pi_measure_space n mss =
    (pi_m_space n mss, pi_measurable_sets n mss, pi_measure n mss)`;

val pi_id_msp_def = Define `pi_id_msp = ({(λi:num. ARB:α)},POW {(λi:num. ARB:α)},
    (λfs:(num->α)->bool. if fs = ∅ then (0:real) else 1))`;

val measurability_preserving_def = Define `measurability_preserving a b = {f |
    sigma_algebra a ∧ sigma_algebra b ∧ BIJ f (space a) (space b) ∧
    (∀s. s ∈ subsets a ⇒ IMAGE f s ∈ subsets b) ∧
    ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a}`;

val measure_preserving_def = Define `measure_preserving m0 m1 = {f |
    f ∈ measurability_preserving (m_space m0,measurable_sets m0) (m_space m1,measurable_sets m1) ∧
    ∀s. s ∈ measurable_sets m0 ⇒ (measure m0 s = measure m1 (IMAGE f s))}`;

val isomorphic_def = Define `isomorphic m0 m1 ⇔ ∃f. f ∈ measure_preserving m0 m1`;
*)

Definition pi_pair_def:
    pi_pair 0 f e = (λi. ARB) ∧
    pi_pair (SUC n) f e = (λi. if (i = n) then e else f i)
End

Theorem pi_pair_alt:
  pi_pair (SUC n) f e = f(| n |-> e|)
Proof
  simp[pi_pair_def, FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> metis_tac[]
QED


Definition pi_cross_def:
    pi_cross (n:num) fs s = {pi_pair n f e | f ∈ fs ∧ e ∈ s}
End

Definition pi_prod_sets_def:
    pi_prod_sets n fsts sts = {pi_cross n fs s | fs ∈ fsts ∧ s ∈ sts}
End

(* pi_m_space 0 mn = {(λi. ARB)} *)
Definition pi_m_space_def:
    pi_m_space 0 mn = {(λi. ARB)} ∧
    pi_m_space (SUC n) mn = pi_cross (SUC n) (pi_m_space n mn) (m_space (mn n))
End

Definition pi_measurable_sets_def:
    pi_measurable_sets 0 mn = POW {(λi. ARB)} ∧
    pi_measurable_sets (SUC n) mn = subsets (sigma (pi_m_space (SUC n) mn)
        (pi_prod_sets (SUC n) (pi_measurable_sets n mn) (measurable_sets (mn n))))
End

Theorem pi_measurable_sets_alt =
  pi_measurable_sets_def
    |> SIMP_RULE (srw_ss()) [pi_prod_sets_def, pi_cross_def, pi_pair_alt]

Definition pi_sig_alg_def:
    pi_sig_alg n mn = (pi_m_space n mn,pi_measurable_sets n mn)
End

Definition pi_measure_rec_lex_def:
    pi_measure_rec_lex (INL (n,_)) = (n,0) ∧
    pi_measure_rec_lex (INR (n,_)) = (n,SUC 0)
End

(* (λfs. if (fs = ∅) then 0 else 1) *)
Definition pi_measure_rec_def:
    pi_measure 0 mn = C 𝟙 (λi. ARB) ∧
    pi_measure (SUC n) mn = (λfs. ∫⁺ (mn n) (λe. ∫⁺ (pi_measure_space n mn) (λf. 𝟙 fs (pi_pair (SUC n) f e)))) ∧
    pi_measure_space n mn = (pi_m_space n mn, pi_measurable_sets n mn, pi_measure n mn)
Termination
    WF_REL_TAC `inv_image ($< LEX $<) pi_measure_rec_lex` >> simp[pi_measure_rec_lex_def]
End

Theorem pi_measure_def:
    (∀mn. pi_measure 0 mn = C 𝟙 (λi. ARB)) ∧
    (∀n mn. pi_measure (SUC n) mn =
        (λfs. ∫⁺ (mn n) (λe. ∫⁺ (pi_measure_space n mn) (λf. 𝟙 fs (pi_pair (SUC n) f e)))))
Proof
    simp[pi_measure_rec_def]
QED

Theorem pi_measure_space_def:
    ∀n mn. pi_measure_space n mn = (pi_m_space n mn,pi_measurable_sets n mn,pi_measure n mn)
Proof
    simp[pi_measure_rec_def]
QED

Theorem pi_measure_alt =
        pi_measure_def |> SIMP_RULE (srw_ss()) [pi_pair_alt, combinTheory.C_DEF]

Theorem m_space_pi_measure_space:
    ∀n mn. m_space (pi_measure_space n mn) = pi_m_space n mn
Proof
    simp[pi_measure_space_def]
QED

Theorem measurable_sets_pi_measure_space:
    ∀n mn. measurable_sets (pi_measure_space n mn) = pi_measurable_sets n mn
Proof
    simp[pi_measure_space_def]
QED

Theorem measure_pi_measure_space:
    ∀n mn. measure (pi_measure_space n mn) = pi_measure n mn
Proof
    simp[pi_measure_space_def]
QED

Theorem sig_alg_pi_measure_space:
    ∀n mn. sig_alg (pi_measure_space n mn) = pi_sig_alg n mn
Proof
    simp[pi_measure_space_def,pi_sig_alg_def]
QED

Theorem space_pi_sig_alg:
    ∀n mn. space (pi_sig_alg n mn) = pi_m_space n mn
Proof
    simp[pi_sig_alg_def]
QED

Theorem subsets_pi_sig_alg:
    ∀n mn. subsets (pi_sig_alg n mn) = pi_measurable_sets n mn
Proof
    simp[pi_sig_alg_def]
QED

val PI_MSP_ss = named_rewrites_with_names "PI_MSP" $ map name_to_thname [
    "m_space_pi_measure_space","measurable_sets_pi_measure_space","measure_pi_measure_space",
    "sig_alg_pi_measure_space","space_pi_sig_alg","subsets_pi_sig_alg"];

val _ = augment_srw_ss [PI_MSP_ss];

Definition pow_measure_space_def:
    pow_measure_space n m = pi_measure_space n (K m)
End

Definition measurability_preserving_def:
    measurability_preserving a b = {f |
        sigma_algebra a ∧ sigma_algebra b ∧ BIJ f (space a) (space b) ∧
        (∀s. s ∈ subsets a ⇒ IMAGE f s ∈ subsets b) ∧
        ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a}
End

Definition measure_preserving_def:
    measure_preserving m0 m1 = {f |
        f ∈ measurability_preserving (sig_alg m0) (sig_alg m1) ∧
        ∀s. s ∈ measurable_sets m0 ⇒ (measure m0 s = measure m1 (IMAGE f s))}
End

Definition isomorphic_def:
    isomorphic m0 m1 ⇔ ∃f. f ∈ measure_preserving m0 m1
End

(*
Definition pi_id_msp_def:
    pi_id_msp = ({(λi:num. ARB:α)},POW {(λi:num. ARB:α)},
        (λfs:(num->α)->bool. if fs = ∅ then (0:extreal) else 1))
End
*)

(* alternate representations *)

Theorem in_measurability_preserving:
    ∀f a b. f ∈ measurability_preserving a b ⇔
        sigma_algebra a ∧ sigma_algebra b ∧ BIJ f (space a) (space b) ∧
        (∀s. s ∈ subsets a ⇒ IMAGE f s ∈ subsets b) ∧
        ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a
Proof
    simp[measurability_preserving_def]
QED

Theorem in_measurability_preserving_alt:
    ∀f a b. f ∈ measurability_preserving a b ⇔ ∃ar br.
        sigma (space a) ar = a ∧ sigma (space b) br = b ∧ subset_class (space a) ar ∧
        subset_class (space b) br ∧ BIJ f (space a) (space b) ∧
        (∀s. s ∈ ar ⇒ IMAGE f s ∈ br) ∧ (∀s. s ∈ br ⇒ PREIMAGE f s ∩ space a ∈ ar)
Proof
    rw[in_measurability_preserving] >> eq_tac >> strip_tac
    >- (qexistsl_tac [`subsets a`,`subsets b`] >> simp[SIGMA_STABLE,SIGMA_ALGEBRA_SUBSET_CLASS]) >>
    NTAC 2 $ (dxrule_then mp_tac SIGMA_ALGEBRA_SIGMA >> simp[] >> strip_tac) >> CONJ_TAC
    >- (qspecl_then [`space a`,`b`,`f`] mp_tac PREIMAGE_SIGMA_ALGEBRA >> simp[iffLR BIJ_ALT] >>
        `ar ⊆ IMAGE (λs. PREIMAGE f s ∩ space a) (subsets b)` suffices_by (NTAC 2 strip_tac >>
            dxrule_all_then mp_tac SIGMA_PROPERTY_WEAK >> simp[] >> rw[SUBSET_DEF] >>
            first_x_assum $ dxrule_then assume_tac >> gvs[] >> rename [`PREIMAGE f s`] >>
            drule_all_then assume_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[BIJ_IMAGE_PREIMAGE,SF SFY_ss]) >>
        simp[SUBSET_DEF] >> qx_gen_tac `s` >> strip_tac >> first_x_assum $ drule_then assume_tac >>
        qexists_tac `IMAGE f s` >> irule_at Any EQ_SYM >> irule_at Any BIJ_PREIMAGE_IMAGE >>
        qexists_tac `space b` >> simp[] >> irule_at Any SIGMA_ALGEBRA_SUBSET_SPACE >> simp[] >>
        map_every (fn sp => qspecl_then sp mp_tac SIGMA_SUBSET_SUBSETS) [[`space a`,`ar`],[`space b`,`br`]] >>
        simp[SUBSET_DEF])
    >- (drule_all_then mp_tac IMAGE_SIGMA_ALGEBRA >>
        `br ⊆ IMAGE (IMAGE f) (subsets a)` suffices_by (NTAC 2 strip_tac >>
            dxrule_all_then mp_tac SIGMA_PROPERTY_WEAK >> simp[] >> rw[SUBSET_DEF] >>
            first_x_assum $ dxrule_then assume_tac >> gvs[] >> rename [`IMAGE f s`] >>
            drule_all_then assume_tac SIGMA_ALGEBRA_SUBSET_SPACE >> simp[BIJ_PREIMAGE_IMAGE,SF SFY_ss]) >>
        simp[SUBSET_DEF] >> qx_gen_tac `s` >> strip_tac >> first_x_assum $ drule_then assume_tac >>
        qexists_tac `PREIMAGE f s ∩ space a` >> irule_at Any EQ_SYM >> irule_at Any BIJ_IMAGE_PREIMAGE >>
        qexists_tac `space b` >> simp[] >> irule_at Any SIGMA_ALGEBRA_SUBSET_SPACE >> simp[] >>
        map_every (fn sp => qspecl_then sp mp_tac SIGMA_SUBSET_SUBSETS) [[`space a`,`ar`],[`space b`,`br`]] >>
        simp[SUBSET_DEF])
QED

Theorem measure_preserving_alt:
    ∀m0 m1. measure_preserving m0 m1 = {f |
        f ∈ measurability_preserving (sig_alg m0) (sig_alg m1) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))}
Proof
    rw[measure_preserving_def,EXTENSION] >> eq_tac >> rw[] >>
    Q.RENAME_TAC [`f ∈ measurability_preserving _ _`]
    >- (first_x_assum (qspec_then `PREIMAGE f s ∩ m_space m0` assume_tac) >>
        rfs[measurability_preserving_def] >> `(IMAGE f (PREIMAGE f s ∩ m_space m0)) = s` suffices_by simp[] >>
        irule BIJ_IMAGE_PREIMAGE >> qexists_tac `m_space m1` >> simp[] >>
        qspec_then `sig_alg m1` assume_tac SIGMA_ALGEBRA_SUBSET_SPACE >> rfs[])
    >- (first_x_assum (qspec_then `IMAGE f s` assume_tac) >> rfs[measurability_preserving_def] >>
        `(PREIMAGE f (IMAGE f s) ∩ m_space m0) = s` suffices_by simp[] >> irule BIJ_PREIMAGE_IMAGE >>
        simp[GSYM RIGHT_EXISTS_AND_THM] >> qexists_tac `m_space m1` >> simp[] >>
        qspec_then `sig_alg m0` assume_tac SIGMA_ALGEBRA_SUBSET_SPACE >> rfs[])
QED

Theorem measure_preserving_full:
    ∀m0 m1. measure_preserving m0 m1 = {f |
        f ∈ measurability_preserving (m_space m0,measurable_sets m0) (m_space m1,measurable_sets m1) ∧
        (∀s. s ∈ measurable_sets m0 ⇒ (measure m0 s = measure m1 (IMAGE f s))) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))}
Proof
    rw[EXTENSION] >> eq_tac >> rw[]
    >- (fs[measure_preserving_def])
    >- (fs[measure_preserving_def])
    >- (fs[measure_preserving_alt])
    >- (simp[measure_preserving_def])
QED

Theorem in_measure_preserving:
    ∀f m0 m1. f ∈ measure_preserving m0 m1 ⇔
        f ∈ measurability_preserving (sig_alg m0) (sig_alg m1) ∧
        ∀s. s ∈ measurable_sets m0 ⇒ (measure m0 s = measure m1 (IMAGE f s))
Proof
    simp[measure_preserving_def]
QED

Theorem in_measure_preserving_alt:
    ∀f m0 m1. f ∈ measure_preserving m0 m1 ⇔
        f ∈ measurability_preserving (sig_alg m0) (sig_alg m1) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))
Proof
    simp[measure_preserving_alt]
QED

Theorem in_measure_preserving_full:
    ∀f m0 m1. f ∈ measure_preserving m0 m1 ⇔
        f ∈ measurability_preserving (sig_alg m0) (sig_alg m1) ∧
        (∀s. s ∈ measurable_sets m0 ⇒ (measure m0 s = measure m1 (IMAGE f s))) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))
Proof
    simp[measure_preserving_full]
QED

Theorem in_m_space_pi_measure_space_imp:
    ∀n mss f. f ∈ m_space (pi_measure_space n mss) ⇒ f ∈ ((count n) --> (m_space ∘ mss))
Proof
    NTAC 2 strip_tac >> Induct_on `n` >- simp[COUNT_ZERO,DFUNSET] >>
    strip_tac >> simp[pi_measure_space_def,pi_m_space_def,pi_cross_def,pi_pair_def] >>
    rw[] >> rename [`f ∈ pi_m_space n mss`] >> fs[pi_measure_space_def] >>
    last_x_assum $ drule_then assume_tac >> fs[DFUNSET,count_def] >> rw[]
QED

Theorem measurability_preserving_measurable:
    ∀a b f. f ∈ measurability_preserving a b ⇒ f ∈ measurable a b
Proof
    simp[in_measurability_preserving,BIJ_ALT,IN_MEASURABLE]
QED

Theorem measure_preserving_measurability_preserving:
    ∀m0 m1 f. f ∈ measure_preserving m0 m1 ⇒ f ∈ measurability_preserving (sig_alg m0) (sig_alg m1)
Proof
    simp[in_measure_preserving]
QED

Theorem measure_preserving_measurable:
    ∀m0 m1 f. f ∈ measure_preserving m0 m1 ⇒ f ∈ measurable (sig_alg m0) (sig_alg m1)
Proof
    simp[measure_preserving_measurability_preserving,measurability_preserving_measurable]
QED

Definition measurability_contracting_def:
    measurability_contracting a b = {f |
        sigma_algebra a ∧ sigma_algebra b ∧ SURJ f (space a) (space b) ∧
        ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a}
End

Definition measure_contracting_def:
    measure_contracting m0 m1 = {f |
        f ∈ measurability_contracting (sig_alg m0) (sig_alg m1) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))}
End

Theorem in_measurability_contracting:
    ∀f a b. f ∈ measurability_contracting a b ⇔
        sigma_algebra a ∧ sigma_algebra b ∧ SURJ f (space a) (space b) ∧
        ∀s. s ∈ subsets b ⇒ PREIMAGE f s ∩ space a ∈ subsets a
Proof
    simp[measurability_contracting_def]
QED

Theorem in_measure_contracting:
    ∀m0 m1 f. f ∈ measure_contracting m0 m1 ⇔
        f ∈ measurability_contracting (sig_alg m0) (sig_alg m1) ∧
        ∀s. s ∈ measurable_sets m1 ⇒ (measure m1 s = measure m0 (PREIMAGE f s ∩ m_space m0))
Proof
    simp[measure_contracting_def]
QED

Theorem in_measurability_contracting_alt:
    ∀a b f. f ∈ measurability_contracting a b ⇔ ∃ar br.
        sigma (space a) ar = a ∧ sigma (space b) br = b ∧ subset_class (space a) ar ∧
        subset_class (space b) br ∧ SURJ f (space a) (space b) ∧
        ∀s. s ∈ br ⇒ PREIMAGE f s ∩ space a ∈ ar
Proof
    rw[in_measurability_contracting] >> eq_tac >> strip_tac
    >- (qexistsl_tac [`subsets a`,`subsets b`] >> simp[SIGMA_STABLE,SIGMA_ALGEBRA_SUBSET_CLASS]) >>
    map_every qabbrev_tac [`asp = space a`,`bsp = space b`] >> NTAC 2 $ pop_assum kall_tac >>
    NTAC 2 $ last_x_assum $ SUBST1_TAC o SYM >> NTAC 2 $ irule_at Any SIGMA_ALGEBRA_SIGMA >> simp[] >>
    `sigma_algebra (bsp,{s | s ⊆ bsp ∧ PREIMAGE f s ∩ asp ∈ subsets (sigma asp ar)})` suffices_by (
        rw[sigma_def] >> first_x_assum (fn th => first_x_assum $ C (resolve_then Any assume_tac) th) >>
        fs[] >> pop_assum $ irule o cj 2 >> simp[] >> simp[SUBSET_DEF] >> fs[subset_class_def,SUBSET_DEF]) >>
    simp[SIGMA_ALGEBRA_ALT_SPACE,subset_class_def,FUNSET] >>
    NTAC 2 $ dxrule_then assume_tac SIGMA_ALGEBRA_SIGMA >> rpt CONJ_TAC
    >- (`PREIMAGE f bsp ∩ asp = asp` by (simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >> fs[SURJ_DEF]) >>
        pop_assum SUBST1_TAC >> NTAC 2 $ dxrule_then assume_tac SIGMA_ALGEBRA_SPACE >> fs[SPACE_SIGMA])
    >- (rw[] >> dxrule_all_then mp_tac SIGMA_ALGEBRA_COMPL >> simp[SPACE_SIGMA] >>
        `PREIMAGE f (bsp DIFF s) ∩ asp = asp DIFF PREIMAGE f s ∩ asp` suffices_by simp[] >>
        rw[EXTENSION] >> eq_tac  >> rw[] >> fs[SURJ_DEF])
    >- (qx_gen_tac `sn` >> rw[] >- (simp[SUBSET_DEF,IN_BIGUNION_IMAGE] >> rw[] >> fs[SUBSET_DEF,SF SFY_ss]) >>
        simp[PREIMAGE_BIGUNION,GSYM BIGUNION_IMAGE_INTER_RIGHT,IMAGE_IMAGE] >>
        irule SIGMA_ALGEBRA_COUNTABLE_UNION >> simp[] >> rw[SUBSET_DEF] >> simp[])
QED

Theorem measurability_contracting_measurable:
    ∀a b f. f ∈ measurability_contracting a b ⇒ f ∈ measurable a b
Proof
    simp[in_measurability_contracting,SURJ_DEF,IN_MEASURABLE,FUNSET]
QED

(* Isomorphism as an Equivalence Relation *)

Theorem isomorphic_refl:
    ∀m. measure_space m ⇒ isomorphic m m
Proof
    rw[isomorphic_def,measure_preserving_def,measurability_preserving_def,space_def,subsets_def] >>
    qexists_tac `I` >> simp[MEASURE_SPACE_SIGMA_ALGEBRA,IMAGE_I,PREIMAGE_I,BIJ_I] >>
    rw[] >> `s ∩ m_space m = s` suffices_by simp[] >> irule SUBSET_INTER1 >>
    simp[MEASURABLE_SETS_SUBSET_SPACE]
QED

Theorem measurability_preserving_LINV:
    ∀f a b. f ∈ measurability_preserving a b ⇒ LINV f (space a) ∈ measurability_preserving b a
Proof
    rpt gen_tac >> simp[in_measurability_preserving,BIJ_LINV_BIJ] >> rw[] >>
    first_x_assum $ drule_then assume_tac >> imp_res_tac SIGMA_ALGEBRA_SUBSET_SPACE >>
    simp[IMAGE_LINV,PREIMAGE_LINV,SF SFY_ss]
QED

Theorem measure_preserving_LINV:
    ∀f m0 m1. f ∈ measure_preserving m0 m1 ⇒ LINV f (m_space m0) ∈ measure_preserving m1 m0
Proof
    rpt gen_tac >> simp[Once in_measure_preserving_alt,Once in_measure_preserving] >> strip_tac >>
    drule_then mp_tac measurability_preserving_LINV >> simp[] >> DISCH_THEN kall_tac >> rw[] >>
    irule EQ_SYM >> irule IRULER >> irule IMAGE_LINV >> qexists_tac `m_space m1` >>
    qspecl_then [`sig_alg m1`,`s`] mp_tac SIGMA_ALGEBRA_SUBSET_SPACE >> fs[in_measurability_preserving]
QED

Theorem isomorphic_sym_imp:
    ∀m0 m1. isomorphic m0 m1 ⇒ isomorphic m1 m0
Proof
    rw[isomorphic_def] >> qexists_tac `LINV f (m_space m0)` >> simp[measure_preserving_LINV]
QED

Theorem isomorphic_sym:
    ∀m0 m1. isomorphic m0 m1 ⇔ isomorphic m1 m0
Proof
    rw[] >> eq_tac >> simp[isomorphic_sym_imp]
QED

Theorem measurability_preserving_comp:
    ∀f g a b c. f ∈ measurability_preserving a b ∧ g ∈ measurability_preserving b c ⇒
        g ∘ f ∈ measurability_preserving a c
Proof
    rpt gen_tac >> simp[in_measurability_preserving,BIJ_COMPOSE,SF SFY_ss] >> strip_tac >>
    simp[IMAGE_COMPOSE] >> rw[] >>
    `PREIMAGE (g ∘ f) s ∩ space a = PREIMAGE f (PREIMAGE g s ∩ space b) ∩ space a` suffices_by simp[PREIMAGE_COMP] >>
    simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >> fs[BIJ_ALT,FUNSET]
QED

Theorem measure_preserving_comp:
    ∀f g m0 m1 m2. f ∈ measure_preserving m0 m1 ∧ g ∈ measure_preserving m1 m2 ⇒
        g ∘ f ∈ measure_preserving m0 m2
Proof
    rpt gen_tac >> simp[in_measure_preserving] >> strip_tac >>
    drule_all_then mp_tac measurability_preserving_comp >> simp[IMAGE_COMPOSE] >> DISCH_THEN kall_tac >> rw[] >>
    first_x_assum irule >> fs[in_measurability_preserving]
QED

Theorem isomorphic_trans:
    ∀m0 m1 m2. isomorphic m0 m1 ∧ isomorphic m1 m2 ⇒ isomorphic m0 m2
Proof
    rw[isomorphic_def] >> rename [`f ∈ measure_preserving m0 m1`,`g ∈ measure_preserving m1 m2`] >>
    qexists_tac `g ∘ f` >> simp[measure_preserving_comp,SF SFY_ss]
QED

Theorem isomorphic_equiv_on_measure_spaces:
    isomorphic equiv_on measure_space
Proof
    simp[equiv_on_def,IN_APP,isomorphic_refl,Once isomorphic_sym] >> rw[] >>
    dxrule_all_then mp_tac isomorphic_trans >> simp[]
QED

(* isomorphism implying measure space *)

Theorem measure_space_isomorphic:
    ∀m0 m1. measure_space m0 ∧ isomorphic m0 m1 ⇒ measure_space m1
Proof
    rw[] >> rw[measure_space_def,positive_def,countably_additive_def]
    >- (fs[isomorphic_def,in_measure_preserving,measurability_preserving_def])
    >- (fs[isomorphic_def,in_measure_preserving,measurability_preserving_def] >>
        drule_then assume_tac MEASURE_SPACE_EMPTY_MEASURABLE >>
        first_x_assum $ dxrule_then mp_tac >> simp[IMAGE_EMPTY] >>
        DISCH_THEN $ SUBST1_TAC o SYM >> simp[MEASURE_EMPTY])
    >- (fs[isomorphic_def,in_measure_preserving_alt,measurability_preserving_def] >>
        irule MEASURE_POSITIVE >> simp[])
    >- (rename [`IMAGE sn 𝕌(:num)`] >>
        fs[isomorphic_def,in_measure_preserving_alt,measurability_preserving_def] >>
        irule EQ_SYM >> irule EQ_TRANS >>
        qexists_tac `suminf (measure m0 ∘ (λn. PREIMAGE f (sn n) ∩ m_space m0))` >>
        irule_at Any MEASURE_COUNTABLY_ADDITIVE >> fs[FUNSET,o_DEF] >>
        simp[PREIMAGE_BIGUNION,GSYM IMAGE_COMPOSE,o_DEF,BIGUNION_IMAGE_INTER_RIGHT] >>
        rw[] >> first_x_assum $ dxrule_then mp_tac >> simp[DISJOINT_ALT])
QED

Theorem sigma_finite_measure_space_isomorphic:
    ∀m0 m1. sigma_finite_measure_space m0 ∧ isomorphic m0 m1 ⇒ sigma_finite_measure_space m1
Proof
    simp[sigma_finite_measure_space_def,measure_space_isomorphic,SF SFY_ss] >>
    rw[sigma_finite_def] >> rename [`IMAGE sn 𝕌(:num)`] >>
    rfs[isomorphic_def,in_measure_preserving,measurability_preserving_def,FUNSET] >>
    qexists_tac `λn. IMAGE f (sn n)` >> qpat_x_assum `∀s. _ ⇒ _ = _` $ mp_tac o GSYM >>
    simp[] >> DISCH_THEN kall_tac >> drule_then assume_tac $ cj 2 $ iffLR BIJ_DEF >>
    dxrule_then SUBST1_TAC $ GSYM $ iffLR IMAGE_SURJ >>
    drule_then (qspec_then `IMAGE f` $ SUBST1_TAC o SYM) IRULER >>
    simp[IMAGE_BIGUNION,GSYM IMAGE_COMPOSE,o_DEF]
QED

(* pispace measure space *)

Theorem SUBSET_pi_cross:
    ∀n fs gt s t. fs ⊆ gt ∧ s ⊆ t ⇒ pi_cross n fs s ⊆ pi_cross n gt t
Proof
    rw[pi_cross_def,SUBSET_DEF] >> qexistsl_tac [`f`,`e`] >> simp[]
QED

Theorem pi_m_space_oob:
    ∀n mn f i. f ∈ pi_m_space n mn ∧ n ≤ i ⇒ f i = ARB
Proof
    Induct_on `n` >> rw[pi_m_space_def] >> fs[pi_cross_def,pi_pair_def] >> simp[SF SFY_ss]
QED

Theorem in_pi_m_space_in_m_space:
    ∀n m mn f. m < n ∧ f ∈ pi_m_space n mn ⇒ f m ∈ m_space (mn m)
Proof
    Induct_on `n` >> rw[] >> fs[pi_m_space_def,pi_cross_def,pi_pair_def] >>
    Cases_on `m = n` >> simp[]
QED

Theorem pi_pair_eq:
    ∀n mn f g x y. f ∈ pi_m_space n mn ∧ g ∈ pi_m_space n mn ∧
        pi_pair (SUC n) f x = pi_pair (SUC n) g y ⇒ f = g ∧ x = y
Proof
    REVERSE $ rw[] >> pop_assum mp_tac >> rw[pi_pair_def,FUN_EQ_THM]
    >- (pop_assum $ qspec_then `n` mp_tac >> simp[]) >> rename [`f i = g i`] >>
    pop_assum $ qspec_then `i` mp_tac >> rw[] >> NTAC 2 $ dxrule_then assume_tac pi_m_space_oob >> simp[]
QED

Theorem sigma_algebra_pi_sig_alg:
    ∀n mn. (∀i. i < n ⇒ measure_space (mn i)) ⇒ sigma_algebra (pi_sig_alg n mn)
Proof
    Induct_on `n` >> rw[] >> simp[pi_sig_alg_def,pi_measurable_sets_def,SIGMA_REDUCE]
    >- simp[pi_m_space_def,POW_SIGMA_ALGEBRA] >>
    irule SIGMA_ALGEBRA_SIGMA >> simp[subset_class_def] >> rw[pi_prod_sets_def,pi_m_space_def] >>
    irule SUBSET_pi_cross >> simp[MEASURABLE_SETS_SUBSET_SPACE] >>
    last_x_assum $ qspec_then `mn` assume_tac >> rfs[pi_sig_alg_def] >>
    dxrule_then assume_tac SIGMA_ALGEBRA_SUBSET_CLASS >> fs[subset_class_def]
QED

Theorem in_measure_preserving_pi_pair:
    ∀n mn. sigma_finite_measure_space (pi_measure_space n mn) ∧ sigma_finite_measure_space (mn n) ⇒
        (λ(f,e). pi_pair (SUC n) f e) ∈
        measure_preserving (pi_measure_space n mn × mn n) (pi_measure_space (SUC n) mn)
Proof
    REVERSE $ rw[in_measure_preserving]
    >- (rename [`fs ∈ _`] >> simp[prod_measure_space_def,prod_measure_def,pi_measure_def] >>
        irule IRULER >> simp[FUN_EQ_THM] >> qx_gen_tac `e` >>
        irule pos_fn_integral_cong >> simp[iffLR sigma_finite_measure_space_def,INDICATOR_FN_POS] >>
        qx_gen_tac `f` >> DISCH_TAC >> rw[indicator_fn_def,EXISTS_PROD]
        >- (pop_assum mp_tac >> simp[] >> qexistsl_tac [`f`,`e`] >> simp[]) >>
        rename [`pi_pair (SUC n) f e = pi_pair (SUC n) g d`] >>
        dxrule_at_then Any assume_tac MEASURABLE_SETS_SUBSET_SPACE >>
        rfs[measure_space_prod_measure,SUBSET_DEF] >> pop_assum $ drule_then assume_tac >>
        fs[m_space_prod_measure_space] >> dxrule_all_then assume_tac pi_pair_eq >> fs[]) >>
    fs[sigma_finite_measure_space_def] >> NTAC 2 $ qpat_x_assum `sigma_finite _` kall_tac >>
    `BIJ (λ(f,e). pi_pair (SUC n) f e) (m_space (pi_measure_space n mn × mn n)) (pi_m_space (SUC n) mn)` by (
        simp[m_space_prod_measure_space,pi_m_space_def] >>
        simp[BIJ_ALT,EXISTS_UNIQUE_ALT,EXISTS_PROD,FORALL_PROD,FUNSET,pi_cross_def] >> CONJ_TAC
        >- (qx_genl_tac [`f`,`e`] >> rw[] >> qexistsl_tac [`f`,`e`] >> simp[]) >>
        rw[] >> qexistsl_tac [`f`,`e`] >> qx_genl_tac [`g`,`d`] >> eq_tac >> strip_tac >> gvs[] >>
        dxrule_all_then mp_tac pi_pair_eq >> simp[]) >>
    `∀fs s. pi_cross (SUC n) fs s = IMAGE (λ(f,e). pi_pair (SUC n) f e) (fs × s)` by (rw[] >>
        simp[EXTENSION,EXISTS_PROD] >> qx_gen_tac `f` >> simp[pi_cross_def]) >>
    simp[in_measurability_preserving_alt] >>
    qexistsl_tac [`prod_sets (measurable_sets (pi_measure_space n mn)) (measurable_sets (mn n))`,
        `pi_prod_sets (SUC n) (pi_measurable_sets n mn) (measurable_sets (mn n))`] >> rw[]
    >- simp[prod_measure_space_def,prod_sigma_def,SIGMA_REDUCE]
    >- simp[pi_sig_alg_def,pi_measurable_sets_def,SIGMA_REDUCE]
    >- (rw[subset_class_def,m_space_prod_measure_space] >> irule SUBSET_CROSS >>
        NTAC 2 $ dxrule_then assume_tac MEASURABLE_SETS_SUBSET_SPACE >> rfs[])
    >- (rw[subset_class_def,pi_m_space_def,pi_prod_sets_def] >> map_every irule [IMAGE_SUBSET,SUBSET_CROSS] >>
        NTAC 2 $ dxrule_then assume_tac MEASURABLE_SETS_SUBSET_SPACE >> rfs[])
    >- (rename [`fs × s`] >> simp[pi_prod_sets_def] >> qexistsl_tac [`fs`,`s`] >> simp[])
    >- (rename [`fr ∈ _`] >> gvs[pi_prod_sets_def] >> qexistsl_tac [`fs`,`s`] >> simp[] >>
        dxrule_then irule BIJ_PREIMAGE_IMAGE >> simp[m_space_prod_measure_space] >> irule SUBSET_CROSS >>
        NTAC 2 $ dxrule_then assume_tac MEASURABLE_SETS_SUBSET_SPACE >> rfs[])
QED

Theorem sigma_finite_measure_space_pi_measure_space:
    ∀n mn. (∀i. i < n ⇒ sigma_finite_measure_space (mn i)) ⇒ sigma_finite_measure_space (pi_measure_space n mn)
Proof
    NTAC 2 gen_tac >> Induct_on `n` >> rw[]
    >- (simp[pi_measure_space_def,pi_m_space_def,pi_measurable_sets_def,pi_measure_def] >>
        qspec_then `({(λi. ARB)},POW {(λi. ARB)})`
            (irule o SIMP_RULE (srw_ss ()) []) sigma_finite_measure_space_fixed_state_measure >>
        simp[POW_SIGMA_ALGEBRA]) >>
    `isomorphic (pi_measure_space n mn × mn n) (pi_measure_space (SUC n) mn)` suffices_by (
        DISCH_TAC >> dxrule_at_then Any irule sigma_finite_measure_space_isomorphic >>
        simp[sigma_finite_measure_space_prod_measure]) >>
    fs[] >> pop_assum $ qspec_then `n` assume_tac >> fs[] >> simp[isomorphic_def] >>
    qexists_tac `λ(f,e). pi_pair (SUC n) f e` >> simp[in_measure_preserving_pi_pair]
QED

Theorem measure_space_pi_measure_space:
    ∀n mn. (∀i. i < n ⇒ sigma_finite_measure_space (mn i)) ⇒ measure_space (pi_measure_space n mn)
Proof
    simp[sigma_finite_measure_space_pi_measure_space,iffLR sigma_finite_measure_space_def]
QED

Theorem prob_space_pi_measure_space:
    ∀n mn. (∀i. i < n ⇒ prob_space (mn i)) ⇒ prob_space (pi_measure_space n mn)
Proof
    Induct_on `n` >> rw[] >> simp[prob_space_def] >> irule_at Any measure_space_pi_measure_space >>
    simp[prob_space_sigma_finite_measure_space]
    >- simp[pi_measure_def,pi_m_space_def,indicator_fn_def] >>
    simp[pi_measure_def] >> last_x_assum $ qspec_then `mn` assume_tac >> rfs[] >>
    fs[prob_space_def] >> irule EQ_TRANS >> qexists_tac `∫⁺ (mn n) (λx. 1)` >>
    irule_at Any pos_fn_integral_cong >> simp[pos_fn_integral_const] >> CONJ_ASM2_TAC
    >- simp[] >> qx_gen_tac `e` >> rw[] >> irule EQ_TRANS >>
    qexists_tac `∫⁺ (pi_measure_space n mn) (λx. 1)` >> irule_at Any pos_fn_integral_cong >>
    simp[pos_fn_integral_const,INDICATOR_FN_POS] >> qx_gen_tac `f` >> rw[] >>
    simp[indicator_fn_def,pi_m_space_def,pi_cross_def] >> metis_tac[]
QED

(* Misc results *)

Theorem pi_measure_space_cross:
    ∀n mn fs s. (∀i. i < SUC n ⇒ measure_space (mn i)) ∧
        fs ∈ pi_measurable_sets n mn ∧ s ∈ measurable_sets (mn n) ⇒
        pi_cross (SUC n) fs s ∈ pi_measurable_sets (SUC n) mn
Proof
    rw[pi_measurable_sets_def,prod_sigma_def] >> irule IN_SIGMA >> simp[pi_prod_sets_def] >>
    qexistsl_tac [`fs`,`s`] >> simp[]
QED

Theorem pi_measure_pi_cross:
    ∀n mn fs s. (∀i. i < SUC n ⇒ sigma_finite_measure_space (mn i)) ∧
        fs ∈ pi_measurable_sets n mn ∧ s ∈ measurable_sets (mn n) ⇒
        pi_measure (SUC n) mn (pi_cross (SUC n) fs s) = pi_measure n mn fs * measure (mn n) s
Proof
    rw[] >> qspecl_then [`n`,`mn`] mp_tac in_measure_preserving_pi_pair >>
    qspecl_then [`n`,`mn`] assume_tac sigma_finite_measure_space_pi_measure_space >>
    rfs[] >> simp[in_measure_preserving] >> rw[] >> pop_assum $ qspec_then `fs × s` mp_tac >>
    map_every (qspecl_then [`pi_measure_space n mn`,`mn n`,`fs`,`s`] mp_tac)
        [prod_measure_cross,MEASURE_SPACE_CROSS] >>
    simp[] >> NTAC 3 $ DISCH_THEN kall_tac >> irule IRULER >>
    simp[pi_cross_def,IMAGE_DEF,UNCURRY] >> simp[EXTENSION,EXISTS_PROD]
QED

Theorem null_set_pi_crossr:
    ∀n mn fs s. (∀i. i < SUC n ⇒ sigma_finite_measure_space (mn i)) ∧
        fs ∈ pi_measurable_sets n mn ∧ s ∈ null_set (mn n) ⇒
        pi_cross (SUC n) fs s ∈ null_set (pi_measure_space (SUC n) mn)
Proof
    rw[IN_NULL_SET,null_set_def] >- (irule pi_measure_space_cross >> simp[]) >>
    drule_all_then SUBST1_TAC pi_measure_pi_cross >> simp[]
QED

Theorem null_set_pi_crossl:
    ∀n mn fs s. (∀i. i < SUC n ⇒ sigma_finite_measure_space (mn i)) ∧
        fs ∈ null_set (pi_measure_space n mn) ∧ s ∈ measurable_sets (mn n) ⇒
        pi_cross (SUC n) fs s ∈ null_set (pi_measure_space (SUC n) mn)
Proof
    rw[IN_NULL_SET,null_set_def] >- (irule pi_measure_space_cross >> simp[]) >>
    drule_all_then SUBST1_TAC pi_measure_pi_cross >> simp[]
QED

Theorem null_set_pi_cross:
    ∀n mn fs s. (∀i. i < SUC n ⇒ sigma_finite_measure_space (mn i)) ∧
        fs ∈ null_set (pi_measure_space n mn) ∧ s ∈ null_set (mn n) ⇒
        pi_cross (SUC n) fs s ∈ null_set (pi_measure_space (SUC n) mn)
Proof
    rw[IN_NULL_SET,null_set_def] >- (irule pi_measure_space_cross >> simp[]) >>
    drule_all_then SUBST1_TAC pi_measure_pi_cross >> simp[]
QED

Theorem pi_measure_space_pi_m_space:
    ∀n mn. (∀i. i < n ⇒ measure_space (mn i)) ⇒ pi_m_space n mn ∈ pi_measurable_sets n mn
Proof
    Induct_on `n` >> rw[pi_m_space_def,pi_measurable_sets_def] >- (simp[POW_DEF]) >>
    irule IN_SIGMA >> simp[pi_prod_sets_def] >> qexistsl_tac [`pi_m_space n mn`,`m_space (mn n)`] >>
    simp[MEASURE_SPACE_SPACE]
QED

Theorem pi_measure_space_AE_per_dim:
    ∀n mn P. (∀i. i < n ⇒ sigma_finite_measure_space (mn i)) ∧ (∀i. i < n ⇒ AE x::(mn i). P i x) ⇒
        AE xi::(pi_measure_space n mn). ∀i. i < n ⇒ P i (xi i)
Proof
    Induct_on `n` >> rw[] >- (irule AE_T >> simp[] >> simp[measure_space_pi_measure_space]) >>
    last_x_assum $ qspecl_then [`mn`,`P`] assume_tac >> rfs[] >>
    `n < SUC n` by simp[] >> first_x_assum $ dxrule_then assume_tac >>
    fs[AE_ALT] >> rename [`null_set (pi_measure_space n mn) Npi`,`null_set (mn n) Nn`] >>
    qexists_tac `pi_cross (SUC n) (pi_m_space n mn) Nn ∪ pi_cross (SUC n) Npi (m_space (mn n))` >> rw[]
    >- (fs[GSYM IN_NULL_SET] >>
        map_every (irule_at (Pos last)) [NULL_SET_UNION,null_set_pi_crossl,null_set_pi_crossr] >>
        simp[pi_measure_space_pi_m_space,MEASURE_SPACE_SPACE,measure_space_pi_measure_space]) >>
    fs[SUBSET_DEF] >> qx_gen_tac `hi` >> simp[pi_m_space_def,pi_cross_def] >> rw[] >>
    Cases_on `n = i` >> gvs[] >> rename [`SUC n`] >| [DISJ1_TAC,DISJ2_TAC] >>
    qexistsl_tac [`f`,`e`] >> simp[] >> first_x_assum irule >> simp[]
    >| [all_tac,qexists_tac `i`] >> fs[pi_pair_def]
QED

(* change of working space *)

Theorem iso_valid_psf_comp:
    ∀sa sb g s e a. sigma_algebra sa ∧ sigma_algebra sb ∧ g ∈ measurability_preserving sa sb ∧
        valid_psf sb s e a ⇒ valid_psf sa s (λi. PREIMAGE g (e i) ∩ space sa) a
Proof
    simp[valid_psf_def,measurability_preserving_def]
QED

Theorem epi_valid_psf_comp:
    ∀sa sb g s e a. sigma_algebra sa ∧ sigma_algebra sb ∧ g ∈ measurability_contracting sa sb ∧
        valid_psf sb s e a ⇒ valid_psf sa s (λi. PREIMAGE g (e i) ∩ space sa) a
Proof
    simp[valid_psf_def,measurability_contracting_def]
QED

(*
Theorem iso_psf_comp:
    ∀sa sb g s e a x. sigma_algebra sa ∧ sigma_algebra sb ∧ g ∈ measurability_preserving sa sb ∧
        valid_psf sb s e a ∧ x ∈ space sa ⇒ psf s e a (g x) = psf s (λi. PREIMAGE g (e i) ∩ space sa) a x
Proof
    rw[psf_def] >> irule EXTREAL_SUM_IMAGE_EQ >> rw[] >> fs[valid_psf_def] >- (rw[indicator_fn_def]) >>
    DISJ1_TAC >> qx_gen_tac `i` >> DISCH_TAC >> NTAC 2 $ irule_at Any pos_not_neginf >>
    NTAC 2 $ irule_at Any le_mul >> simp[INDICATOR_FN_POS]
QED
*)

Theorem psf_comp:
    ∀sa sb g s e a x. sigma_algebra sa ∧ sigma_algebra sb ∧
        valid_psf sb s e a ∧ x ∈ space sa ⇒ psf s e a (g x) = psf s (λi. PREIMAGE g (e i) ∩ space sa) a x
Proof
    rw[psf_def] >> irule EXTREAL_SUM_IMAGE_EQ >> rw[] >> fs[valid_psf_def] >- (rw[indicator_fn_def]) >>
    DISJ1_TAC >> qx_gen_tac `i` >> DISCH_TAC >> NTAC 2 $ irule_at Any pos_not_neginf >>
    NTAC 2 $ irule_at Any le_mul >> simp[INDICATOR_FN_POS]
QED

Theorem iso_valid_psf_seq_comp:
    ∀sa sb g si ei ai. sigma_algebra sa ∧ sigma_algebra sb ∧ g ∈ measurability_preserving sa sb ∧
        valid_psf_seq sb si ei ai ⇒ valid_psf_seq sa si (λi j. PREIMAGE g (ei i j) ∩ space sa) ai
Proof
    rw[valid_psf_seq_def] >- (irule iso_valid_psf_comp >> simp[] >> qexists_tac `sb` >> simp[]) >>
    fs[ext_mono_increasing_def] >> qx_genl_tac [`i`,`j`] >> rw[] >>
    `g x ∈ space sb` by fs[measurability_preserving_def,BIJ_ALT,FUNSET] >>
    NTAC 2 $ first_x_assum $ dxrule_then assume_tac >> pop_assum mp_tac >>
    qmatch_abbrev_tac `_ Σa Σb ⇒ _ Σc Σd` >> `Σc = Σa ∧ Σd = Σb` suffices_by simp[] >>
    UNABBREV_ALL_TAC >> NTAC 2 (irule_at Any $ GSYM psf_comp >> qexists_tac `sb`) >> simp[]
QED

Theorem epi_valid_psf_seq_comp:
    ∀sa sb g si ei ai. sigma_algebra sa ∧ sigma_algebra sb ∧ g ∈ measurability_contracting sa sb ∧
        valid_psf_seq sb si ei ai ⇒ valid_psf_seq sa si (λi j. PREIMAGE g (ei i j) ∩ space sa) ai
Proof
    rw[valid_psf_seq_def] >- (irule epi_valid_psf_comp >> simp[] >> qexists_tac `sb` >> simp[]) >>
    fs[ext_mono_increasing_def] >> qx_genl_tac [`i`,`j`] >> rw[] >>
    `g x ∈ space sb` by fs[measurability_contracting_def,SURJ_DEF] >>
    NTAC 2 $ first_x_assum $ dxrule_then assume_tac >> pop_assum mp_tac >>
    qmatch_abbrev_tac `_ Σa Σb ⇒ _ Σc Σd` >> `Σc = Σa ∧ Σd = Σb` suffices_by simp[] >>
    UNABBREV_ALL_TAC >> NTAC 2 (irule_at Any $ GSYM psf_comp >> qexists_tac `sb`) >> simp[]
QED

(*
Theorem iso_psf_seq_lim_comp:
    ∀sa sb g si ei ai x. sigma_algebra sa ∧ sigma_algebra sb ∧ g ∈ measurability_preserving sa sb ∧
        valid_psf_seq sb si ei ai ∧ x ∈ space sa ⇒
        psf_seq_lim si ei ai (g x) = psf_seq_lim si (λi j. PREIMAGE g (ei i j) ∩ space sa) ai x
Proof
    rw[psf_seq_lim_def] >> fs[valid_psf_seq_def] >> irule IRULER >> irule IMAGE_CONG >>
    rw[] >> simp[psf_comp,SF SFY_ss]
QED
*)

Theorem psf_seq_lim_comp:
    ∀sa sb g si ei ai x. sigma_algebra sa ∧ sigma_algebra sb ∧
        valid_psf_seq sb si ei ai ∧ x ∈ space sa ⇒
        psf_seq_lim si ei ai (g x) = psf_seq_lim si (λi j. PREIMAGE g (ei i j) ∩ space sa) ai x
Proof
    rw[psf_seq_lim_def] >> fs[valid_psf_seq_def] >> irule IRULER >> irule IMAGE_CONG >>
    rw[] >> simp[psf_comp,SF SFY_ss]
QED

Theorem iso_psf_integral_comp:
    ∀m0 m1 g s e a. measure_space m0 ∧ measure_space m1 ∧ g ∈ measure_preserving m0 m1 ∧
        valid_psf (sig_alg m1) s e a ⇒
        psf_integral (measure m1) s e a = psf_integral (measure m0) s (λi. PREIMAGE g (e i) ∩ m_space m0) a
Proof
    rw[in_measure_preserving_alt,valid_psf_def,psf_integral_def] >> irule EXTREAL_SUM_IMAGE_EQ >>
    simp[] >> DISJ1_TAC >> rw[] >> irule pos_not_neginf >> irule le_mul >> simp[] >>
    irule MEASURE_POSITIVE >> fs[in_measurability_preserving]
QED

Theorem epi_psf_integral_comp:
    ∀m0 m1 g s e a. measure_space m0 ∧ measure_space m1 ∧ g ∈ measure_contracting m0 m1 ∧
        valid_psf (sig_alg m1) s e a ⇒
        psf_integral (measure m1) s e a = psf_integral (measure m0) s (λi. PREIMAGE g (e i) ∩ m_space m0) a
Proof
    rw[in_measure_contracting,valid_psf_def,psf_integral_def] >> irule EXTREAL_SUM_IMAGE_EQ >>
    simp[] >> DISJ1_TAC >> rw[] >> irule pos_not_neginf >> irule le_mul >> simp[] >>
    irule MEASURE_POSITIVE >> fs[in_measurability_contracting]
QED

Theorem iso_pos_fn_integral_comp:
    ∀m0 m1 g f. measure_space m0 ∧ measure_space m1 ∧ g ∈ measure_preserving m0 m1 ∧
        f ∈ Borel_measurable (sig_alg m1) ∧ (∀x. x ∈ m_space m1 ⇒ 0 ≤ f x) ⇒ ∫⁺ m1 f = ∫⁺ m0 (f ∘ g)
Proof
    rw[] >> qspecl_then [`sig_alg m1`,`f`] mp_tac pos_fn_sup_psf_seq >> simp[] >> DISCH_TAC >> fs[] >>
    qspecl_then [`m1`,`f`,`si`,`ei`,`ai`] mp_tac pos_fn_psf_integral_convergence >>
    simp[] >> DISCH_THEN kall_tac >> drule_then assume_tac $ cj 1 $ iffLR in_measure_preserving >>
    qspecl_then [`m0`,`f ∘ g`,`si`,`(λi j. PREIMAGE g (ei i j) ∩ m_space m0)`,`ai`]
        mp_tac pos_fn_psf_integral_convergence >> simp[] >>
    qspecl_then [`sig_alg m0`,`sig_alg m1`] mp_tac iso_valid_psf_seq_comp >> simp[] >> DISCH_THEN kall_tac >>
    `∀x. x ∈ m_space m0 ⇒ f (g x) = psf_seq_lim si (λi j. PREIMAGE g (ei i j) ∩ m_space m0) ai x` by (
        rw[] >> `g x ∈ m_space m1` by fs[measurability_preserving_def,BIJ_ALT,FUNSET] >>
        first_x_assum $ dxrule_then SUBST1_TAC >>
        qspecl_then [`sig_alg m0`,`sig_alg m1`,`g`,`si`,`ei`,`ai`,`x`] mp_tac psf_seq_lim_comp >> simp[]) >>
    pop_assum $ simp o single >> DISCH_THEN kall_tac >> irule IRULER >> irule IMAGE_CONG >>
    rw[] >> fs[valid_psf_seq_def,iso_psf_integral_comp]
QED

Theorem epi_pos_fn_integral_comp:
    ∀m0 m1 g f. measure_space m0 ∧ measure_space m1 ∧ g ∈ measure_contracting m0 m1 ∧
        f ∈ Borel_measurable (sig_alg m1) ∧ (∀x. x ∈ m_space m1 ⇒ 0 ≤ f x) ⇒ ∫⁺ m1 f = ∫⁺ m0 (f ∘ g)
Proof
    rw[] >> qspecl_then [`sig_alg m1`,`f`] mp_tac pos_fn_sup_psf_seq >> simp[] >> DISCH_TAC >> fs[] >>
    qspecl_then [`m1`,`f`,`si`,`ei`,`ai`] mp_tac pos_fn_psf_integral_convergence >>
    simp[] >> DISCH_THEN kall_tac >> drule_then assume_tac $ cj 1 $ iffLR in_measure_contracting >>
    qspecl_then [`m0`,`f ∘ g`,`si`,`(λi j. PREIMAGE g (ei i j) ∩ m_space m0)`,`ai`]
        mp_tac pos_fn_psf_integral_convergence >> simp[] >>
    qspecl_then [`sig_alg m0`,`sig_alg m1`] mp_tac epi_valid_psf_seq_comp >> simp[] >> DISCH_THEN kall_tac >>
    `∀x. x ∈ m_space m0 ⇒ f (g x) = psf_seq_lim si (λi j. PREIMAGE g (ei i j) ∩ m_space m0) ai x` by (
        rw[] >> `g x ∈ m_space m1` by fs[measurability_contracting_def,SURJ_DEF] >>
        first_x_assum $ dxrule_then SUBST1_TAC >>
        qspecl_then [`sig_alg m0`,`sig_alg m1`,`g`,`si`,`ei`,`ai`,`x`] mp_tac psf_seq_lim_comp >> simp[]) >>
    pop_assum $ simp o single >> DISCH_THEN kall_tac >> irule IRULER >> irule IMAGE_CONG >>
    rw[] >> fs[valid_psf_seq_def,epi_psf_integral_comp]
QED

(* dimensionality reduction *)

Theorem pi_tonelli:
    ∀n mn ff. (∀i. i < SUC n ⇒ sigma_finite_measure_space (mn i)) ∧
        ff ∈ Borel_measurable (pi_sig_alg (SUC n) mn) ∧ (∀f. f ∈ pi_m_space (SUC n) mn ⇒ 0 ≤ ff f) ⇒
        (∀e. e ∈ m_space (mn n) ⇒ (λf. ff (pi_pair (SUC n) f e)) ∈ Borel_measurable (pi_sig_alg n mn)) ∧
        (∀f. f ∈ (pi_m_space n mn) ⇒ (λe. ff (pi_pair (SUC n) f e)) ∈ Borel_measurable (sig_alg (mn n))) ∧
        (λf. ∫⁺ (mn n) (λe. ff (pi_pair (SUC n) f e))) ∈ Borel_measurable (pi_sig_alg n mn) ∧
        (λe. ∫⁺ (pi_measure_space n mn) (λf. ff (pi_pair (SUC n) f e))) ∈ Borel_measurable (sig_alg (mn n)) ∧
        ∫⁺ (pi_measure_space (SUC n) mn) ff =
            ∫⁺ (mn n) (λe. ∫⁺ (pi_measure_space n mn) (λf. ff (pi_pair (SUC n) f e))) ∧
        ∫⁺ (pi_measure_space (SUC n) mn) ff =
            ∫⁺ (pi_measure_space n mn) (λf. ∫⁺ (mn n) (λe. ff (pi_pair (SUC n) f e)))
Proof
    rpt gen_tac >> DISCH_TAC >> fs[] >>
    map_every (fn tm => qspecl_then [tm,`mn`] assume_tac sigma_finite_measure_space_pi_measure_space)
        [`n`,`SUC n`] >> rfs[] >>
    `sigma_finite_measure_space (pi_measure_space n mn × mn n)` by simp[sigma_finite_measure_space_prod_measure] >>
    qspecl_then [`n`,`mn`] assume_tac in_measure_preserving_pi_pair >> rfs[] >>
    `∫⁺ (pi_measure_space (SUC n) mn) ff =
      ∫⁺ (pi_measure_space n mn × mn n) (ff ∘ (λ(f,e). pi_pair (SUC n) f e))` by (
        irule iso_pos_fn_integral_comp >> simp[iffLR sigma_finite_measure_space_def]) >>
    pop_assum SUBST1_TAC >>
    qspecl_then [`pi_measure_space n mn`,`mn n`,`ff ∘ (λ(f,e). pi_pair (SUC n) f e)`] mp_tac TONELLI_ALT >>
    simp[] >> DISCH_THEN irule >>
    irule_at Any $ INST_TYPE [``:α`` |-> ``:(num -> α) # α``,``:β`` |-> ``:(num -> α)``] IN_MEASURABLE_BOREL_COMP >>
    qexistsl_tac [`(λ(f,e). pi_pair (SUC n) f e)`,`ff`,`pi_sig_alg (SUC n) mn`] >> simp[] >>
    fs[sigma_finite_measure_space_def,measure_space_def,SPACE_PROD_SIGMA,
        m_space_prod_measure_space,measurable_sets_prod_measure_space,sig_alg_prod_measure_space,
        in_measure_preserving,in_measurability_preserving,IN_MEASURABLE,BIJ_ALT,FUNSET]
QED

Theorem idx_measurable:
    ∀n m mn. m < n ∧ (∀i. i < n ⇒ measure_space (mn i)) ⇒ C LET m ∈ measurable (pi_sig_alg n mn) (sig_alg (mn m))
Proof
    Induct_on `n` >> rw[] >> simp[IN_MEASURABLE,sigma_algebra_pi_sig_alg] >> CONJ_TAC
    >- simp[FUNSET,in_pi_m_space_in_m_space,SF SFY_ss] >> rw[] >>
    simp[pi_measurable_sets_def] >> irule IN_SIGMA >> simp[pi_prod_sets_def] >>
    last_x_assum $ qspecl_then [`m`,`mn`] assume_tac >> Cases_on `m = n` >> gvs[]
    >- (qexistsl_tac [`pi_m_space m mn`,`s`] >>
        `sigma_algebra (pi_sig_alg m mn)` by simp[sigma_algebra_pi_sig_alg] >>
        dxrule_then assume_tac SIGMA_ALGEBRA_SPACE >> fs[] >> simp[EXTENSION] >>
        qx_gen_tac `g` >> simp[pi_m_space_def,pi_cross_def] >> eq_tac >> rw[]
        >| [all_tac,simp[pi_pair_def],all_tac] >> qexistsl_tac [`f`,`e`] >> simp[]
        >- fs[pi_pair_def] >> irule MEASURE_SPACE_IN_MSPACE >> simp[] >> qexists_tac `s` >> simp[])
    >- (fs[measurable_def] >> first_x_assum $ dxrule_then assume_tac >>
        qexistsl_tac [`PREIMAGE (C LET m) s ∩ pi_m_space n mn`,`m_space (mn n)`] >>
        simp[MEASURE_SPACE_SPACE,EXTENSION] >> qx_gen_tac `g` >> simp[pi_m_space_def,pi_cross_def] >>
        eq_tac >> rw[] >| [all_tac,simp[pi_pair_def],all_tac] >> qexistsl_tac [`f`,`e`] >> simp[] >>
        rfs[pi_pair_def])
QED

Theorem pos_fn_integral_pi_dim:
    ∀n mn f m. m < n ∧ (∀i. i < n ⇒ prob_space (mn i)) ∧ (∀x. x ∈ m_space (mn m) ⇒ 0 ≤ f x) ∧
        f ∈ Borel_measurable (sig_alg (mn m)) ⇒
        ∫⁺ (pi_measure_space n mn) (f ∘ C LET m) = ∫⁺ (mn m) f
Proof
    Induct_on `n` >> rw[] >> qmatch_abbrev_tac `_ _ ff = _` >>
    `(∀i. i < SUC n ⇒ sigma_finite_measure_space (mn i)) ∧
      ff ∈ Borel_measurable (pi_sig_alg (SUC n) mn) ∧ (∀f. f ∈ pi_m_space (SUC n) mn ⇒ 0 ≤ ff f)` by (
        qunabbrev_tac `ff` >> fs[prob_space_sigma_finite_measure_space,prob_space_def] >>
        qspecl_then [`SUC n`,`m`,`mn`] mp_tac idx_measurable >> simp[] >> DISCH_TAC >>
        simp[MEASURABLE_COMP,SF SFY_ss] >> qx_gen_tac `g` >> strip_tac >> first_x_assum irule >>
        fs[IN_MEASURABLE,FUNSET]) >>
    Cases_on `m = n` >> gvs[]
    >- (dxrule_all_then SUBST1_TAC $ cj 5 pi_tonelli >> irule pos_fn_integral_cong >> REVERSE CONJ_ASM1_TAC
        >- fs[prob_space_def] >> qx_gen_tac `e` >> rw[Abbr `ff`,pi_pair_def] >>
        qspecl_then [`pi_measure_space m mn`,`f e`] mp_tac pos_fn_integral_const >> simp[] >>
        `prob_space (pi_measure_space m mn)` suffices_by simp[prob_space_def] >>
        irule prob_space_pi_measure_space >> simp[])
    >- (last_x_assum $ qspecl_then [`mn`,`f`,`m`] mp_tac >> simp[] >> DISCH_THEN $ SUBST1_TAC o SYM >>
        dxrule_all_then SUBST1_TAC $ cj 6 pi_tonelli >> irule pos_fn_integral_cong >> REVERSE CONJ_ASM1_TAC
        >- (csimp[] >> irule_at Any measure_space_pi_measure_space >> simp[prob_space_sigma_finite_measure_space] >>
            qunabbrev_tac `ff` >> rw[] >> first_x_assum irule >> fs[prob_space_def] >>
            qspecl_then [`n`,`m`,`mn`] mp_tac idx_measurable >> simp[IN_MEASURABLE,FUNSET]) >>
        qx_gen_tac `g` >>  rw[Abbr `ff`,pi_pair_def] >> fs[prob_space_def] >>
        qspecl_then [`mn n`,`f (g m)`] mp_tac pos_fn_integral_const >> simp[] >> DISCH_THEN irule >>
        first_x_assum irule >> qspecl_then [`n`,`m`,`mn`] mp_tac idx_measurable >> simp[IN_MEASURABLE,FUNSET])
QED

Theorem integral_pi_dim:
    ∀n mn f m. m < n ∧ (∀i. i < n ⇒ prob_space (mn i)) ∧ f ∈ Borel_measurable (sig_alg (mn m)) ⇒
        ∫ (pi_measure_space n mn) (f ∘ C LET m) = ∫ (mn m) f
Proof
    rw[integral_def] >> `∀x1:extreal x2 x3 x4. x1 = x3 ∧ x2 = x4 ⇒ x1 - x2 = x3 - x4` by simp[] >>
    `(f ∘ C LET m)⁺ = f⁺ ∘ C LET m ∧ (f ∘ C LET m)⁻ = f⁻ ∘ C LET m` by simp[o_DEF,fn_plus_def,fn_minus_def] >>
    map_every pop_assum [SUBST1_TAC,SUBST1_TAC,irule] >> NTAC 2 $ irule_at Any pos_fn_integral_pi_dim >>
    simp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS,FN_PLUS_POS,FN_MINUS_POS]
QED

Theorem integrable_pi_dim:
    ∀n mn f m. m < n ∧ (∀i. i < n ⇒ prob_space (mn i)) ∧ integrable (mn m) f ⇒
        integrable (pi_measure_space n mn) (f ∘ C LET m)
Proof
    rw[] >> fs[integrable_def] >> irule_at Any MEASURABLE_COMP >> qexists_tac `sig_alg (mn m)` >>
    irule_at Any idx_measurable >> simp[prob_space_measure_space] >>
    `∀x:extreal y z. x = y ∧ y ≠ z ⇒ x ≠ z` by simp[] >>
    pop_assum $ NTAC 2 o pop_assum o C (resolve_then Any (irule_at $ Pos last)) >>
    `(f ∘ C LET m)⁺ = f⁺ ∘ C LET m ∧ (f ∘ C LET m)⁻ = f⁻ ∘ C LET m` by simp[o_DEF,fn_plus_def,fn_minus_def] >>
    NTAC 2 $  pop_assum SUBST1_TAC >> NTAC 2 $ irule_at Any pos_fn_integral_pi_dim >>
    simp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS,FN_PLUS_POS,FN_MINUS_POS]
QED

Theorem pos_fn_integral_pi_sum_dim:
    ∀n mn fi. (∀i. i < n ⇒ prob_space (mn i)) ∧ (∀i x. i < n ∧ x ∈ m_space (mn i) ⇒ 0 ≤ fi i x) ∧
        (∀i. i < n ⇒ (fi i) ∈ Borel_measurable (sig_alg (mn i))) ⇒
        ∫⁺ (pi_measure_space n mn) (λxi. (∑ (λi. fi i (xi i)) (count n))) = ∑ (λi. ∫⁺ (mn i) (fi i)) (count n)
Proof
    rw[] >> irule EQ_TRANS >> qexists_tac `∑ (λi. ∫⁺ (pi_measure_space n mn) ((fi i) ∘ C LET i)) (count n)` >>
    irule_at Any EXTREAL_SUM_IMAGE_EQ >> simp[] >>
    qspecl_then [`pi_measure_space n mn`,`λi. (fi i) ∘ C LET i`,`count n`] mp_tac pos_fn_integral_sum >>
    simp[] >> DISCH_THEN $ irule_at Any >> irule_at Any measure_space_pi_measure_space >>
    irule_at Any OR_INTRO_THM1 >> simp[prob_space_sigma_finite_measure_space,GSYM FORALL_IMP_CONJ_THM] >>
    `∀i. i < n ⇒ C LET i ∈ measurable (pi_sig_alg n mn) (sig_alg (mn i))` by (
        rw[] >> irule idx_measurable >> simp[iffLR prob_space_def]) >>
    qx_gen_tac `i` >> DISCH_TAC >> CONJ_ASM2_TAC >| [simp[] >> pop_assum kall_tac,rw[]]
    >- (irule pos_not_neginf >> irule pos_fn_integral_pos >> simp[iffLR prob_space_def])
    >- (first_x_assum irule >> fs[IN_MEASURABLE,FUNSET])
    >- (irule MEASURABLE_COMP >> qexists_tac `sig_alg (mn i)` >> simp[])
    >- (irule pos_fn_integral_pi_dim >> simp[])
QED

Theorem integral_pi_sum_dim:
    ∀n mn fi. (∀i. i < n ⇒ prob_space (mn i)) ∧ (∀i. i < n ⇒ integrable (mn i) (fi i)) ⇒
        ∫ (pi_measure_space n mn) (λxi. (∑ (λi. fi i (xi i)) (count n))) = ∑ (λi. ∫ (mn i) (fi i)) (count n)
Proof
    rw[] >> irule EQ_TRANS >> qexists_tac `∑ (λi. ∫ (pi_measure_space n mn) ((fi i) ∘ C LET i)) (count n)` >>
    irule_at Any EXTREAL_SUM_IMAGE_EQ' >> simp[] >>
    qspecl_then [`pi_measure_space n mn`,`λi. (fi i) ∘ C LET i`,`count n`] mp_tac integral_sum_pure >>
    simp[] >> DISCH_THEN $ irule_at Any >> irule_at Any measure_space_pi_measure_space >>
    simp[prob_space_sigma_finite_measure_space,GSYM FORALL_IMP_CONJ_THM] >>
    `∀i. i < n ⇒ C LET i ∈ measurable (pi_sig_alg n mn) (sig_alg (mn i))` by (
        rw[] >> irule idx_measurable >> simp[prob_space_measure_space]) >>
    qx_gen_tac `i` >> DISCH_TAC >> map_every (irule_at Any) [integral_pi_dim,integrable_pi_dim] >>
    simp[integrable_measurable]
QED

Theorem integrable_pi_sum_dim:
    ∀n mn fi. (∀i. i < n ⇒ prob_space (mn i)) ∧ (∀i. i < n ⇒ integrable (mn i) (fi i)) ⇒
        integrable (pi_measure_space n mn) (λxi. (∑ (λi. fi i (xi i)) (count n)))
Proof
    rw[] >>
    qspecl_then [`pi_measure_space n mn`,`λi. fi i ∘ C LET i`,`count n`]
        (irule o SIMP_RULE (srw_ss ()) [LET_THM]) integrable_sum_pure >>
    simp[prob_space_sigma_finite_measure_space,measure_space_pi_measure_space] >>
    rw[] >> irule integrable_pi_dim >> simp[]
QED

(* convoluted measure finagling *)

Theorem pi_measure_rect:
    ∀n mn E. (∀i. i < n ⇒ sigma_finite_measure_space (mn i)) ∧
        E ∈ (count n) ⟶ measurable_sets ∘ mn ⇒
        pi_measure n mn (BIGINTER (IMAGE (λi. PREIMAGE (C LET i) (E i) ∩ pi_m_space n mn) (count n))) =
        ∏ (λi. measure (mn i) (E i)) (count n)
Proof
  Induct_on `n` >> rw[] >- simp[pi_measure_def,indicator_fn_def,EXTREAL_PROD_IMAGE_EMPTY] >>
  Cases_on `n = 0`
  >- (simp[COUNT_ONE,EXTREAL_PROD_IMAGE_SING] >>
      qspecl_then [`0`,`mn`,`pi_m_space 0 mn`,`E 0`] mp_tac pi_measure_pi_cross >>
      simp[] >> fs[DFUNSET,pi_measure_space_pi_m_space] >>
      `pi_measure 0 mn (pi_m_space 0 mn) = 1` by simp[pi_measure_def,pi_m_space_def,indicator_fn_def] >>
      pop_assum SUBST1_TAC >> simp[] >> DISCH_THEN $ SUBST1_TAC o SYM >> irule IRULER >>
      simp[ONE,EXTENSION,pi_m_space_def,pi_cross_def,pi_pair_def,Excl "REDUCE_CONV (arithmetic reduction)"] >>
      rw[] >> eq_tac >> DISCH_TAC >> fs[] >> qexists_tac `e` >> simp[] >- (fs[]) >>
      irule MEASURE_SPACE_IN_MSPACE >> simp[] >> qexists_tac `E 0` >> simp[]) >>
  simp[COUNT_SUC,EXTREAL_PROD_IMAGE_PROPERTY] >>
  first_x_assum $ qspecl_then [`mn`,`E`] assume_tac >> rfs[DFUNSET] >>
  pop_assum $ SUBST1_TAC o SYM >> simp[Once mul_comm] >>
  `BIGINTER (IMAGE (λi. PREIMAGE (C LET i) (E i) ∩ pi_m_space n mn) (count n)) ∈ pi_measurable_sets n mn` by (
    qspecl_then [`pi_measure_space n mn`,`λi. PREIMAGE (C LET i) (E i) ∩ pi_m_space n mn`,`count n`]
                mp_tac MEASURE_SPACE_FINITE_INTER >>
    simp[] >> DISCH_THEN irule >> simp[measure_space_pi_measure_space] >> rw[] >>
    drule idx_measurable >> simp[IN_MEASURABLE]) >>
  simp[GSYM pi_measure_pi_cross] >> pop_assum kall_tac >> irule IRULER >>
  simp[EXTENSION,IN_BIGINTER_IMAGE,pi_m_space_def,pi_cross_def,pi_pair_def] >> qx_gen_tac `xi` >>
  eq_tac >> DISCH_TAC >> gvs[] >- (qexistsl_tac [`f`,`e`] >> simp[]) >>
  qpat_x_assum ‘∀i. _ ⇒ _ ∧ _’ (fn th => map_every (fn n => assume_tac $ cj n th) [1,2]) >>
  pop_assum $ qspec_then `0` assume_tac >> rfs[] >> rw[] >> qexistsl_tac [`f`,`e`] >>
  simp[] >> irule MEASURE_SPACE_IN_MSPACE >> simp[] >> qexists_tac `E n` >> simp[]
QED

Theorem pi_prob_rect:
    ∀n mn E N. (∀i. i < n ⇒ prob_space (mn i)) ∧ E ∈ N ⟶ measurable_sets ∘ mn ∧ N ⊆ count n ∧ N ≠ ∅ ⇒
        pi_measure n mn (BIGINTER (IMAGE (λi. PREIMAGE (C LET i) (E i) ∩ pi_m_space n mn) N)) =
        ∏ (λi. measure (mn i) (E i)) N
Proof
    rw[] >> qabbrev_tac `EP = (λi. if i ∈ N then E i else m_space (mn i))` >>
    qspecl_then [`n`,`mn`,`EP`] assume_tac pi_measure_rect >>
    `∀x1:extreal x2 x3 x4. x2 = x3 ∧ x1 = x2 ∧ x3 = x4 ⇒ x1 = x4` by simp[] >>
    pop_assum $ pop_assum o C (resolve_then (Pos hd) irule) >>
    irule_at Any EXTREAL_PROD_IMAGE_EQ_INTER >> simp[prob_space_sigma_finite_measure_space] >>
    drule_at_then Any (irule_at Any) SUBSET_FINITE_I >> fs[SUBSET_DEF,DFUNSET] >>
    irule_at Any IRULER >> REVERSE (rw[])
    >- (rw[Abbr `EP`] >> irule MEASURE_SPACE_SPACE >> simp[prob_space_measure_space])
    >- (first_x_assum drule >> simp[])
    >- (fs[Abbr `EP`,prob_space_def])
    >- (simp[Abbr `EP`]) >>
    simp[Once EXTENSION,IN_BIGINTER_IMAGE] >> qx_gen_tac `xi` >> simp[Abbr `EP`] >>
    REVERSE eq_tac >> DISCH_TAC >> qx_gen_tac `i` >> DISCH_TAC
    >- (NTAC 2 $ first_x_assum $ drule_then assume_tac >> rfs[]) >>
    fs[GSYM MEMBER_NOT_EMPTY] >> first_assum $ drule_then assume_tac o cj 2 >>
    rw[] >> simp[in_pi_m_space_in_m_space,SF SFY_ss]
QED

Theorem pi_prob_dim:
    ∀n mn s m. m < n ∧ (∀i. i < n ⇒ prob_space (mn i)) ∧ s ∈ measurable_sets (mn m) ⇒
        pi_measure n mn (PREIMAGE (C LET m) s ∩ pi_m_space n mn) = measure (mn m) s
Proof
    rw[] >> qspecl_then [`n`,`mn`,`K s`,`{m}`] mp_tac pi_prob_rect >>
    simp[EXTREAL_PROD_IMAGE_SING,DFUNSET]
QED

Theorem pi_measure_space_dim_indep_vars:
    ∀n mn X A. (∀i. i < n ⇒ prob_space (mn i)) ∧ (∀i. i < n ⇒ random_variable (X i) (mn i) (A i)) ⇒
        indep_vars (pi_measure_space n mn) (λm. X m ∘ C LET m) A (count n)
Proof
  cheat (*
  rw[indep_vars_def,DFUNSET,indep_events_def] >> simp[SF PROB_ss] >>
  qabbrev_tac `PreX = (λi. PREIMAGE (X i) (E i) ∩ m_space (mn i))` >>
  qspecl_then [`n`,`mn`,`PreX`,`N`] assume_tac pi_prob_rect >>
  `∀x1:extreal x2 x3 x4. x2 = x3 ∧ x1 = x2 ∧ x3 = x4 ⇒ x1 = x4` by simp[] >>
       pop_assum $ pop_assum o C (resolve_then (Pos hd) irule) >> simp[] >>
       map_every (irule_at Any) [EXTREAL_PROD_IMAGE_EQ,IRULER,IRULER] >> rw[]
       >- (simp[Abbr `PreX`] >> simp[Once EXTENSION] >> rw[] >>
           eq_tac >> DISCH_TAC >> fs[] >> rename [`i ∈ N`] >> qexists_tac `i` >> simp[]
           >| [irule PREIMAGE_o_INTER,irule $ GSYM PREIMAGE_o_INTER] >>
           fs[SUBSET_DEF] >> rw[] >> first_x_assum $ drule_then assume_tac >>
           drule_all in_pi_m_space_in_m_space >> simp[])
       >- (simp[Abbr `PreX`] >> rename [`i ∈ N`] >>
           `IMAGE (C LET i) (pi_m_space n mn) ⊆ m_space (mn i)` by (fs[SUBSET_DEF] >> rw[] >>
                                                                    first_x_assum $ drule_then assume_tac >> drule_all in_pi_m_space_in_m_space >> simp[]) >>
           qspecl_then [`pi_m_space n mn`,`m_space (mn i)`,`C LET i`,`X i`,`E i`] mp_tac PREIMAGE_o_INTER >>
           simp[] >> DISCH_THEN kall_tac >> irule $ GSYM pi_prob_dim >>
           fs[SUBSET_DEF,random_variable_def,IN_MEASURABLE,SF PROB_ss])
       >- (rw[Abbr `PreX`,DFUNSET] >> fs[SUBSET_DEF,random_variable_def,IN_MEASURABLE,SF PROB_ss])
        *)
QED

val _ = export_theory();
