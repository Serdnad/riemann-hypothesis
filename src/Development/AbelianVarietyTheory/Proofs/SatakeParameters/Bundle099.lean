module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.Columns.Bundle008
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AutomorphicArithmetic.OrbitLabellings.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle002
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle066
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.FramedForms

section Torsor

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem deco_smul (a : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) (p : DecoF E n ST SG Q) :
    (a • p).deco = (a.1, a.2.1) • p.deco := rfl

theorem fr_smul (a : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) (p : DecoF E n ST SG Q) (P : Q) :
    (a • p).fr P = a.1.1 * p.fr P * ((a.2.2 P)⁻¹).1 := rfl

theorem exists_smul_of_deco_eq {p q : DecoF E n ST SG Q} (h : p.deco = q.deco) :
    ∃ c : GLQ E n Q, q = ((1, 1, c) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p := by
  have h' : p.1.1 = q.1.1 := h
  refine ⟨fun P => ⟨(q.fr P)⁻¹ * p.fr P, fun x => ?_⟩, ?_⟩
  · have h1 := q.2 P (((q.fr P)⁻¹ * p.fr P) x)
    have h2 : q.1.2 P (((q.fr P)⁻¹ * p.fr P) x) = p.1.2 P x :=
      LinearEquiv.apply_symm_apply (q.1.2 P) (p.1.2 P x)
    rw [h2, ← h'] at h1
    exact h1.symm.trans (p.2 P x)
  · apply Subtype.ext
    apply Prod.ext
    · exact h'.symm.trans (one_smul (UF E n × GLG (E := E) (n := n) (SG := SG)) p.1.1).symm
    · funext P
      show q.fr P = (1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((q.fr P)⁻¹ * p.fr P)⁻¹
      group

theorem stab_inj (p : DecoF E n ST SG Q) {a b : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q}
    (ha : a • p = p) (hb : b • p = p) (h1 : a.1 = b.1) (h2 : a.2.1 = b.2.1) : a = b := by
  refine Prod.ext h1 (Prod.ext h2 ?_)
  funext P
  have e1 : (a • p).fr P = (b • p).fr P := by rw [ha, hb]
  rw [fr_smul, fr_smul, h1] at e1
  exact inv_injective (Subtype.ext (mul_left_cancel e1))

end Torsor

section Form

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem incl_injective (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) :
    Function.Injective (FrmG.incl Λ Θ) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun x => x.2.1) h
  have h3 := congrArg (fun x => x.2.2) h
  exact Prod.ext h1 (Prod.ext (Subtype.ext h2) (Subtype.ext h3))

theorem grp_finiteIndex (Θ : LevQFam X.E X.K n Q) (h : ∀ R : Q, (Θ R).H.FiniteIndex) :
    Θ.grp.FiniteIndex := by
  have h1 : ∀ R : Q, ((Θ R).H.comap (Pi.evalMonoidHom (fun P : Q => ↥(GLint X.E n P.1)) R)).FiniteIndex := by
    intro R
    refine ⟨?_⟩
    rw [Subgroup.index_comap_of_surjective _ (Function.surjective_eval R)]
    exact (h R).index_ne_zero
  have h2 := Subgroup.finiteIndex_iInf h1
  refine Subgroup.finiteIndex_of_le (H := ⨅ R : Q, (Θ R).H.comap
    (Pi.evalMonoidHom (fun P : Q => ↥(GLint X.E n P.1)) R)) ?_
  intro c hc
  exact (Subgroup.mem_pi _).mpr fun R _ => Subgroup.mem_iInf.mp hc R

theorem chr_root (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)
    (hΘ : ∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) ^ m = 1 := by
  obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2.1
  obtain ⟨k, hk, hk'⟩ := hΘ g.2.2
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  have hk2 : ((Θ.chr g.2.2 : X.Kˣ) : X.K) ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, hk', Units.val_one]
  rw [Units.val_mul, mul_pow, pow_mul, hc, one_pow, one_mul, mul_comm m k, pow_mul, hk2, one_pow]

theorem frmGSD_ok (hX : X.Ok) (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (hC : C.Eqv)
    (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (hfi : ∀ R : Q, (Θ R).H.FiniteIndex)
    (hΘ : ∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) :
    (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ).Ok := by
  refine { fin_orb := ?_, fin_stab := ?_, nab_smul := ?_, del_smul := ?_, inv := ?_ }
  · obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have := grp_finiteIndex Θ hfi
    let T : Set (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) := {d | d ∈ s ∧ ∃ p : DecoF X.E n ST SG Q, p.deco = d}
    have hT : Finite T := hs.subset fun d hd => hd.1
    let S := frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ
    refine Finite.of_surjective (fun x : T × (GLQ X.E n Q ⧸ Θ.grp) =>
      S.cls (((1, 1, (x.2.out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • x.1.2.2.choose)) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)
      have hq : (((g⁻¹, 1, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • (p : DecoF X.E n ST SG Q)).deco = d0 := by
        rw [deco_smul, hg, smul_smul]
        simp only [Prod.mk_mul_mk, inv_mul_cancel, mul_one]
        exact one_smul (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) d0
      have hd : d0 ∈ T := ⟨hd0, _, hq⟩
      obtain ⟨c, hc⟩ := exists_smul_of_deco_eq (hd.2.choose_spec.trans hq.symm)
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Θ.grp c⁻¹
      refine ⟨(⟨d0, hd⟩, (c⁻¹ : GLQ X.E n Q)), ?_⟩
      refine (S.cls_eq_iff _ p).mpr ⟨((g⁻¹, 1, h⁻¹) : FrmG Λ Θ), ?_⟩
      show ((g⁻¹, 1, (h : GLQ X.E n Q)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • (p : DecoF X.E n ST SG Q) =
        ((1, 1, ((c⁻¹ : GLQ X.E n Q) : GLQ X.E n Q ⧸ Θ.grp).out⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) •
          hd.2.choose
      have e1 : ((g⁻¹, 1, (h : GLQ X.E n Q)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) =
          (1, 1, (h : GLQ X.E n Q)⁻¹) * (g⁻¹, 1, 1) := by simp
      rw [e1, mul_smul, hc, smul_smul, hh]
      simp
  · intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p)
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ Θ).G p =>
        (⟨((FrmG.incl Λ Θ a.1).1, (FrmG.incl Λ Θ a.1).2.1), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (DecoF.deco p))) ?_
    intro a b hab
    have h0 := congrArg Subtype.val hab
    exact Subtype.ext (incl_injective Λ Θ
      (stab_inj p a.2 b.2 (Prod.mk.inj h0).1 (Prod.mk.inj h0).2))
  · intro g p
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    exact (hC.nab_smul ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1) (DecoF.deco p)).trans
      (map_root_smul _ _ hm hc).symm
  · intro g p
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    exact (hC.del_smul ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1) (DecoF.deco p)).trans
      (map_root_smul _ _ hm hc).symm
  · intro g x y
    obtain ⟨m, hm, hc⟩ := chr_root Λ Θ hΘ g
    show C.pair (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) • C.rho g.1 x)
      (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv g.1 x y, smul_smul]
    show (star ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

theorem main : ∀ {X : Fields} (_ : X.Ok) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (lam : X.Tau → DomWeight n) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q),
    (∀ R : Q, (Θ R).H.FiniteIndex) → (∀ g, ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1) →
    (frmGSD ((roundPk X lam fun d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) => d.1.Lsh).pull DecoF.deco) Λ Θ).Ok := by
  intro X hX n ST SG Q lam Λ Θ h1 h2
  exact frmGSD_ok hX _
    ⟨fun a d => roundPk_nab X _ _ (d.1.Lsh_act a.1.2 a.2), fun a d => roundPk_del X _ _ (d.1.Lsh_act a.1.2 a.2),
      roundPk_inv X _ _ hX.emb_star⟩ Λ Θ h1 h2

end Form

end GlobalTheory.FramedForms
end
end

section

noncomputable section

namespace GlobalTheory.TwU.LowTerm

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

variable {D : D7} {L : SizeData₂ D}

theorem sum_betaI (X : Inst D L) (K : Consts) (ce : ErrC) (j p : ℕ) (hs : ¬ IsSg D p) :
    ∑ r ∈ OrbitPlaces.repsPl X p, OrbitPlaces.betaI X K ce j p r =
      (∑ t ∈ reps X p, max (g0 X K (aL L) (bL L) p j t) 0) +
        ∑ t ∈ reps X p, (FOrb D j p (true, t) - OrbitPlaces.errF L K ce j p (true, t)) := by
  have hd : Disjoint ((reps X p).image (fun t => ((false, t) : OrbitPlaces.Pl D)))
      ((reps X p).image (fun t => ((true, t) : OrbitPlaces.Pl D))) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨t', -, h⟩ := Finset.mem_image.1 h2
    simp at h
  unfold OrbitPlaces.repsPl
  rw [if_neg hs, Finset.sum_union hd, Finset.sum_image (fun a _ b _ h => by simpa using h),
    Finset.sum_image (fun a _ b _ h => by simpa using h)]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [OrbitPlaces.betaI, OrbitPlaces.g0Pl, kindA, hs]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [OrbitPlaces.betaI, OrbitPlaces.g0Pl, kindA]

theorem FInert_sub_EatI (X : Inst D L) (K : Consts) (ce : ErrC) {p j : ℕ} (hp : p.Prime) (hc : IsResidueClassZero D p)
    (hh : HEv D p) (hs : ¬ IsSg D p) (hj : j ∈ SizeData₂.lifts D) :
    FInert D j p - EatI L K ce j p ≤
      ∑ t ∈ reps X p, (FOrb D j p (true, t) - OrbitPlaces.errF L K ce j p (true, t)) := by
  have h := OrbitPlaces.sumI X K ce p hp (Or.inl ⟨hc, hh⟩) j hj
  rw [sum_betaI X K ce j p hs] at h
  linarith

theorem sum_dG_le {m n : ℕ} (hm : 1 ≤ m) {d : ℕ → ℕ} (h0 : d 0 = 0) (hj : ∀ j, d j ≤ n) :
    ∑ j ∈ Finset.range m, (d j : ℝ) ≤ ((m : ℝ) - 1) * n := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ', h0]
  have : ∑ j ∈ Finset.range k, (d (j + 1) : ℝ) ≤ ∑ _j ∈ Finset.range k, (n : ℝ) :=
    Finset.sum_le_sum fun j _ => by exact_mod_cast hj _
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  push_cast
  linarith

theorem lowS_le : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC)
    (Xe : ErrX D) (dG : ℕ → ℕ), L.FDef → dG 0 = 0 →
    (∀ j, dG j ≤ padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam) →
    WeilJacquetShalikaLaw.lowS L Xe K ce 1 u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ t ∈ reps X (D.what₂.places.resChar w),
      if ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n then
        FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0) -
      ∑ j ∈ Finset.range D.R.m, (dG j : ℝ) := by
  intro D u w hg L X K ce Xe dG hF h0 hd
  have hm : 1 ≤ D.R.m := le_trans one_le_two D.R.two_le_m
  have hloss := sum_dG_le hm h0 hd
  have hc : IsResidueClassZero D (D.what₂.places.resChar w) := hg.2.2.1
  have hs : ¬ IsSg D (D.what₂.places.resChar w) := by
    intro h
    have h' : D.host.cls (D.what₂.places.resChar w) = _ := h
    rw [hg.2.2.1] at h'
    exact absurd h' (by decide)
  have hev : HEv D (D.what₂.places.resChar w) := hEv_of_hNeZero hg.1 hg.2.2.2.1
  have hh := hev.ne_zero
  have hne : ∀ i : Fin 2, D.what₂.places.resChar w ≠ D.host.g i := fun i h => hg.2.2.2.2.1 (h ▸ D.host.g_level i)
  have h2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := by rw [hg.2.2.1]; decide
  have h4 : D.what₂.places.resChar w ∉ L.gTypes := by simp [SizeData₂.gTypes, hne]
  have hcard : ((SizeData₂.lifts D).card : ℝ) = D.R.m := by simp [SizeData₂.lifts]
  have hterm : ∀ j ∈ SizeData₂.lifts D, L.F j w - WeilJacquetShalikaLaw.ES L Xe K ce u j w =
      (if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        FInert D j (D.what₂.places.resChar w) - EatI L K ce j (D.what₂.places.resChar w) else 0) - WeilJacquetShalikaLaw.vDG D u w := by
    intro j hj
    rw [hF j hj w]
    unfold Fval FvalP WeilJacquetShalikaLaw.ES Eval WeilJacquetShalikaLaw.vDG
    simp only [if_neg (hne 0), if_neg (hne 1), if_neg (WeilJacquetShalikaLaw.residue_char_ne_level hg), if_neg h2, if_neg h4]
    by_cases hX : (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n
    · have hA : (IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
          (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n := ⟨Or.inl hc, hX⟩
      have hB : ¬ (IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) = 0) := fun h => hh h.2
      simp only [if_pos hA, if_neg hB, if_pos hX]
      unfold FInert
      rw [if_neg hB]
      ring
    · have hA : ¬ ((IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
          (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n) := fun h => hX h.2
      simp only [if_neg hA, if_neg hX]
      ring
  have hsum : WeilJacquetShalikaLaw.lowS L Xe K ce 1 u w = (∑ j ∈ Finset.Icc 1 D.R.m,
      if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        FInert D j (D.what₂.places.resChar w) - EatI L K ce j (D.what₂.places.resChar w) else 0) -
      ((D.R.m : ℝ) - 1) * WeilJacquetShalikaLaw.vDG D u w := by
    unfold WeilJacquetShalikaLaw.lowS
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    have hl : SizeData₂.lifts D = Finset.Icc 1 D.R.m := rfl
    rw [hl]
    ring
  have hle : (∑ j ∈ Finset.Icc 1 D.R.m,
      if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
        FInert D j (D.what₂.places.resChar w) - EatI L K ce j (D.what₂.places.resChar w) else 0) ≤
      ∑ j ∈ Finset.Icc 1 D.R.m, ∑ t ∈ reps X (D.what₂.places.resChar w),
        if (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n then
          FOrb D j (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce j (D.what₂.places.resChar w) (true, t) else 0 := by
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases hX : (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n
    · simp only [if_pos hX]
      exact FInert_sub_EatI X K ce hg.1 hc hev hs hj
    · simp [hX]
  have hv : ((D.R.m : ℝ) - 1) * (padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℝ) =
      ((D.R.m : ℝ) - 1) * WeilJacquetShalikaLaw.vDG D u w := rfl
  rw [hsum]
  linarith

end GlobalTheory.TwU.LowTerm

end
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.LocSepTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem lpChar_zero_unr (w : PlE H) (χ : A.LP w) (hd : A.lpDim χ = 1) (hu : A.unr χ) :
    A.lpChar (A.lpZero w) χ = A.lpZero w := by
  have hu0 := A.lpZero_unr w
  have hc := A.unr_char _ _ hd hu0 hu
  have hcard := A.frobEig_card _ hc
  rw [A.lpDim_char _ _ hd, A.lpDim_zero] at hcard
  calc A.lpChar (A.lpZero w) χ = A.lpUnr w (A.frobEig (A.lpChar (A.lpZero w) χ)) := A.unr_eq_lpUnr _ hc
    _ = A.lpUnr w (A.frobEig (A.lpZero w)) := by rw [Multiset.card_eq_zero.mp hcard, A.frobEig_zero]
    _ = A.lpZero w := (A.unr_eq_lpUnr _ hu0).symm

theorem spehLoc_twist_of_laws (hC : GlobalTheory.RowTie.CharLaws N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H)
    (hz : A.lpChar (A.lpZero w) (A.locG χ w) = A.lpZero w) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  have hsum : ∀ a b : A.LP w, A.lpChar (A.lpSum a b) (A.locG χ w) =
      A.lpSum (A.lpChar a (A.locG χ w)) (A.lpChar b (A.locG χ w)) := fun a b => (hC w a b _ _ 0 hχ hχ).1
  have htw : ∀ (a : A.LP w) (s : ℝ), A.lpChar (A.lpTw a s) (A.locG χ w) = A.lpTw (A.lpChar a (A.locG χ w)) s :=
    fun a s => (hC w a a _ _ s hχ hχ).2.1
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact hz.symm
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, hsum, htw, A.locG_tw]

theorem isoLoc_twist_of_laws (hC : GlobalTheory.RowTie.CharLaws N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H)
    (hz : A.lpChar (A.lpZero w) (A.locG χ w) = A.lpZero w) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  induction S with
  | nil => exact hz.symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [ih, spehLoc_twist_of_laws N A hC p χ w hz, (hC w _ _ _ _ 0 hχ hχ).1]

theorem isoLoc_append_one (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil =>
    change A.lpSum (spehLoc N A q w) (A.lpZero w) = A.lpSum (A.lpZero w) (spehLoc N A q w)
    exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

theorem heckePol_coeff (i : N.Loc) (x : N.X i) (w : PlE H) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ R.nV) :
    (heckePol N i x w).coeff (R.nV - k) =
      (-1 : N.O i) ^ k * ((normV w : ℕ) : N.O i) ^ (k * (k - 1) / 2) * ((N.hT i w k : N.X i → N.O i) x) := by
  unfold heckePol
  exact GlobalTheory.PtLocalEig.coeff_monic_poly_sum R.nV k hk1 hk2
    (fun k' => (-1 : N.O i) ^ k' * ((normV w : ℕ) : N.O i) ^ (k' * (k' - 1) / 2) * ((N.hT i w k' : N.X i → N.O i) x))

theorem main : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → GlobalTheory.RowTie.CharLaws D.nd D.naut →
    (∀ (i i' : D.nd.Loc) (σ : D.what₂.FT) (v : PlE D.host), IsSplitPl D.host v →
      D.naut.locW i σ v = D.naut.locW i' σ v) →
    (∀ i i' : D.nd.Loc, D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' → D.naut.muC i = D.naut.muC i') →
    KillingConditions.LocalisationUniqueness D := by
  intro D M HT hC hW hmu
  unfold KillingConditions.LocalisationUniqueness
  intro i i' _ hj hw σ _ hA hA'
  by_contra hne
  obtain ⟨φ, hφ⟩ := HT.sameO i i' hj hw
  obtain ⟨Sig, hSig, x, hx⟩ := hA
  obtain ⟨Sig', hSig', x', hx'⟩ := hA'
  obtain ⟨v, k, hv, hv', hk1, hk2, hunit⟩ := HT.sep i i' φ hφ hj hw hne x x'
  obtain ⟨p, hp1, hp2⟩ := hx v hv
  obtain ⟨p', hp1', hp2'⟩ := hx' v hv'
  have hinj' : Function.Injective (iotaO D.nd D.naut i') := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i').injective.comp ((D.naut.iotaQ i').injective.comp
      (IsFractionRing.injective (D.nd.O i') (FractionRing (D.nd.O i'))))
  have hmuP : muPart D.nd D.naut i = muPart D.nd D.naut i' := by
    unfold muPart; rw [hmu i i' hj hw]
  have hz := lpChar_zero_unr D.nd D.naut v (D.naut.locG D.naut.etaTinv v) (D.naut.locG_dim _ v)
    (D.naut.etaTinv_def v).1
  have hpar : isoLoc D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) v =
      isoLoc D.nd D.naut (twistIso D.nd D.naut (Sig' ++ [muPart D.nd D.naut i']) D.naut.etaTinv) v := by
    rw [isoLoc_twist_of_laws D.nd D.naut hC _ _ v hz, isoLoc_twist_of_laws D.nd D.naut hC _ _ v hz,
      isoLoc_append_one, isoLoc_append_one, hSig.2.2 v hv.1, hSig'.2.2 v hv'.1, hW i i' σ v hv.1, hmuP]
  have hpp : p.map (φ : D.nd.O i →+* D.nd.O i') = p' := by
    apply Polynomial.map_injective (iotaO D.nd D.naut i') hinj'
    rw [Polynomial.map_map, hp1', ← hpar, ← hp1]
    congr 1
    exact RingHom.ext fun z => (hφ z).symm
  set n := D.R.nV - k
  have e1 : IsLocalRing.residue (D.nd.O i) (p.coeff n) =
      IsLocalRing.residue (D.nd.O i) ((heckePol D.nd i x v).coeff n) := by
    have := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P n) hp2
    simpa only [Polynomial.coeff_map] using this
  have e2 : IsLocalRing.residue (D.nd.O i') (p'.coeff n) =
      IsLocalRing.residue (D.nd.O i') ((heckePol D.nd i' x' v).coeff n) := by
    have := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P n) hp2'
    simpa only [Polynomial.coeff_map] using this
  have e3 := GlobalTheory.PtLocalEig.residue_map_equiv φ e1
  have hcp : φ (p.coeff n) = p'.coeff n := by
    rw [← hpp, Polynomial.coeff_map]; rfl
  have hφc : φ ((-1 : D.nd.O i) ^ k * ((normV v : ℕ) : D.nd.O i) ^ (k * (k - 1) / 2) *
      ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x)) = (-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2) *
      φ ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [hcp, e2, heckePol_coeff D.nd i x v k hk1 hk2, heckePol_coeff D.nd i' x' v k hk1 hk2, hφc] at e3
  have hq := GlobalTheory.PtLocalEig.normV_unit D i' v hv'.2.1
  have hc : IsUnit ((-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2)) :=
    ((isUnit_one.neg).pow k).mul (hq.pow _)
  have hdiff : IsLocalRing.residue (D.nd.O i')
      ((-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2) *
        (φ ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) - (D.nd.hT i' v k : D.nd.X i' → D.nd.O i') x')) = 0 := by
    rw [mul_sub, map_sub, e3, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hdiff
  exact hdiff (hc.mul hunit)

end GlobalTheory.LocSepTie
end
end
