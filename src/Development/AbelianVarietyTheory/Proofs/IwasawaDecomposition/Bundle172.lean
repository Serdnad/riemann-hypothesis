module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle099
import Formalism.LocalToGlobal.Columns.Bundle008
import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.Col2.DilFv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem exists_red_equiv {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (I : Ideal R) (u : M ≃ₗ[R] M') :
    ∃ e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] (M' ⧸ (I • (⊤ : Submodule R M'))),
      ∀ x, e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (u x) := by
  have h : (I • (⊤ : Submodule R M)).map (u : M →ₗ[R] M') = I • (⊤ : Submodule R M') := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  refine ⟨(Submodule.Quotient.equiv _ _ u h).extendScalarsOfSurjective Ideal.Quotient.mk_surjective, fun x => rfl⟩

theorem exists_red_dual {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (u : M →ₗ[R] R ⧸ I) :
    ∃ φ : (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I] (R ⧸ I), ∀ x, φ (Submodule.Quotient.mk x) = u x := by
  have h : (I • (⊤ : Submodule R M)) ≤ LinearMap.ker u := by
    refine Submodule.smul_le.2 fun r hr x _ => ?_
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]
  exact ⟨(Submodule.liftQ _ u h).extendScalarsOfSurjective Ideal.Quotient.mk_surjective, fun x => rfl⟩

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) {T : ℕ}

theorem fv_mk (h : A.Ok T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have hex : ∃ φ : Module.Dual (Res P.1) (A.lv P c), ∀ x : A.N c.1 (S.rep c),
      φ (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x :=
    exists_red_dual P.1.asIdeal
      { toFun := fun x : A.N c.1 (S.rep c) => A.f c.1 (S.rep c) P x
        map_add' := fun x y => h.f_add _ _ P x x.2 y y.2
        map_smul' := fun a x => h.f_smul _ _ P a x x.2 }
  unfold TDat.fv
  rw [dite_eq_left hex]
  exact hex.choose_spec x

theorem exists_act_equiv (h : A.Ok T) (b : S.β) (g : S.G b) (d : S.D b) (M : Submodule (𝓞 E) (Fin n → E))
    (hM : A.N b (g • d) = M) :
    ∃ u : A.N b d ≃ₗ[𝓞 E] M, ∀ x, (u x : Fin n → E) = (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ (x : Fin n → E) := by
  subst hM
  have h1 : ∀ x : Fin n → E, (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ
      ((S.gam b g⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  have h2 : ∀ x : Fin n → E, (S.gam b g⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ
      ((S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  refine ⟨{ toFun := fun x => ⟨(S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ x.1, (h.N_act b g d x.1).2 x.2⟩
            invFun := fun y => ⟨(S.gam b g⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ y.1,
              (h.N_act b g d _).1 (by rw [h1]; exact y.2)⟩
            map_add' := fun x y => Subtype.ext (Matrix.mulVec_add _ x.1 y.1)
            map_smul' := fun a x => Subtype.ext (Matrix.mulVec_smul _ a x.1)
            left_inv := fun x => Subtype.ext (h2 _)
            right_inv := fun y => Subtype.ext (h1 _) }, fun x => rfl⟩

theorem dil_fv : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → ∀ P a c,
    ∃ e : A.lv P (S.cl c.1 (A.diaPt P a c)) ≃ₗ[Res P.1] A.lv P c,
      ∀ x, A.fv P (S.cl c.1 (A.diaPt P a c)) x = (a : Res P.1) * A.fv P c (e x) := by
  intro E K _ _ _ _ n S ST A T _ h P a c
  obtain ⟨g, hmv⟩ : ∃ g : S.G c.1, g • S.rep (S.cl c.1 (A.diaPt P a c)) = A.diaPt P a c :=
    (MulAction.orbitRel (S.G c.1) (S.D c.1)).symm (Quotient.exact (S.rp_spec c.1 (Quotient.mk _ (A.diaPt P a c))))
  obtain ⟨u, hu⟩ := exists_act_equiv A h c.1 g (S.rep (S.cl c.1 (A.diaPt P a c)))
    (A.N c.1 (S.rep c)) (by rw [hmv]; exact h.dia_N _ _ _ _)
  obtain ⟨e, he⟩ := exists_red_equiv P.1.asIdeal u
  refine ⟨e, fun x => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have e1 := fv_mk A h P (S.cl c.1 (A.diaPt P a c)) x
  have e2 := fv_mk A h P c (u x)
  have e3 := h.f_act c.1 g (S.rep (S.cl c.1 (A.diaPt P a c))) P x
  rw [hmv, ← hu] at e3
  have e4 := h.dia_f c.1 P a (S.rep c) (u x)
  refine e1.trans (e3.symm.trans (e4.trans ?_))
  exact congrArg _ (e2.symm.trans (congrArg _ (he x).symm))

end GlobalTheory.Mem.Col2.DilFv
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem frm_free_zero {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (hX : X.Ok) (hPr : Pr.Ok)
    (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) {Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ : LevFam X.E X.K (R.N 0) Pr.vGs) (hΛ : Λ = colLev Ch 0) (Θ : LevQFam X.E X.K (R.N 0) Q) (g : FrmG Λ Θ)
    (p : DecoF X.E (R.N 0) (Pr.vT u) Pr.vGs Q) (hp : FrmG.incl Λ Θ g • p = p) : g = 1 := by
  subst hΛ
  have hpos : 0 < (Pr.vG 0).card := by
    rw [hPr.vG_card 0, Fields.f, hX.card_Tau]
    exact Module.finrank_pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hw' : w ∈ Pr.vGs := by
    classical
    unfold Primes.vGs
    exact Finset.mem_union_left _ hw
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hmem : (g.2.1 : GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs)) ⟨w, hw'⟩ ∈ (colLev Ch 0 ⟨w, hw'⟩).H :=
    (Subgroup.mem_pi _).mp g.2.1.2 ⟨w, hw'⟩ (Set.mem_univ _)
  rw [colLev_of_lt Ch hm] at hmem
  have ha : ((g.1, (g.2.1 : GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs))) : UF X.E (R.N 0) × GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs)) • p.deco = p.deco :=
    congrArg DecoF.deco hp
  have h1 : ((g.1, (g.2.1 : GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs))) : UF X.E (R.N 0) × GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs)) = 1 :=
    DecoSet.decoration_stabilizer_trivial_unipotent hX hPr p.deco ha 0 ⟨w, hw'⟩ hw (by rw [hN]; exact hbig)
      (isNilpotent_of_mem_HX_zero hN.le hmem)
  apply GlobalTheory.FramedForms.incl_injective
  rw [map_one]
  exact GlobalTheory.FramedForms.stab_inj p hp (one_smul _ p) (Prod.ext_iff.mp h1).1 (Prod.ext_iff.mp h1).2

theorem stepAt_zero_free {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
    (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (hX : X.Ok) (hPr : Pr.Ok)
    (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (hL : ∀ b, L.levG 0 b = colLev Ch 0) :
    (stepAt sel mu cst L Tp u 0).Free := by
  intro b g d hd
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hΛ : levGAt sel mu L Tp 0 b = colLev Ch 0 := by
    obtain ⟨b, hb⟩ := b
    obtain ⟨b0, rfl⟩ := Option.isSome_iff_exists.mp (hb.mpr hm)
    exact hL b0
  exact frm_free_zero Ch hX hPr hbig u _ hΛ _ g d.1.1 (congrArg (fun x => x.1.1) hd)

end GlobalTheory.Mem.Col2
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.StepOk

theorem finite_orbits_of_finite_fibres {G A B : Type} [Group G] [MulAction G A] [MulAction G B] (π : A → B)
    (hπ : ∀ (g : G) a, π (g • a) = g • π a) (hf : ∀ b, {a | π a = b}.Finite)
    [Finite (MulAction.orbitRel.Quotient G B)] : Finite (MulAction.orbitRel.Quotient G A) := by
  haveI : ∀ b, Finite {a | π a = b} := fun b => (hf b).to_subtype
  refine Finite.of_surjective (fun x : Σ q : MulAction.orbitRel.Quotient G B, {a | π a = q.out} =>
    (Quotient.mk _ x.2.1 : MulAction.orbitRel.Quotient G A)) ?_
  intro c
  induction c using Quotient.inductionOn' with
  | h a =>
    have h : (MulAction.orbitRel G B).r (Quotient.mk (MulAction.orbitRel G B) (π a)).out (π a) :=
      Quotient.exact (Quotient.out_eq _)
    obtain ⟨g, hg⟩ := h
    refine ⟨⟨Quotient.mk _ (π a), ⟨g • a, (hπ g a).trans hg⟩⟩, ?_⟩
    exact Quotient.sound ⟨g, rfl⟩

theorem ufGL_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) (x : Fin n → E) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x = γ.1 x :=
  LinearMap.toMatrix'_mulVec (γ.1 : Sp E n →ₗ[E] Sp E n) x

theorem ufGL_conjTranspose_mul {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)ᴴ *
      ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := by
  ext a b
  have h : ∑ i, star (γ.1 (Pi.single a 1) i) * γ.1 (Pi.single b 1) i =
      ∑ i, star ((Pi.single a 1 : Fin n → E) i) * (Pi.single b 1 : Fin n → E) i :=
    γ.2 (Pi.single a 1) (Pi.single b 1)
  have hv : ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
    LinearMap.toMatrix' (γ.1 : Sp E n →ₗ[E] Sp E n) := rfl
  rw [hv, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · rw [Finset.sum_eq_single a]
    · simp [Matrix.one_apply, Pi.single_apply]
    · intro c _ hc
      simp [Pi.single_apply, hc]
    · simp

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem levQ_root (Θ : LevQFam X.E X.K n Q) (h : ∀ P g, ∃ m : ℕ, 0 < m ∧ (Θ P).lam g ^ m = 1) (g : Θ.grp) :
    ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1 := by
  rw [← isOfFinOrder_iff_pow_eq_one]
  unfold LevQFam.chr piChar
  erw [MonoidHom.finsetProd_apply]
  refine Finset.prod_induction _ IsOfFinOrder (fun _ _ ha hb => ha.mul hb) IsOfFinOrder.one fun P _ => ?_
  rw [isOfFinOrder_iff_pow_eq_one]
  exact h P _

theorem eq_one_of_fst (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) (g : FrmG Λ Θ)
    (hg : FrmG.incl Λ Θ g • p = p) (h1 : g.1 = 1) : g = 1 := by
  have hb : FrmG.incl Λ Θ 1 • p = p := by rw [map_one, one_smul]
  have h2 := DecoSet.stab_fst_injective p.deco (a := ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1))
    (b := ((FrmG.incl Λ Θ 1).1, (FrmG.incl Λ Θ 1).2.1)) (congrArg DecoF.deco hg) (congrArg DecoF.deco hb) h1
  exact FramedForms.incl_injective Λ Θ (FramedForms.stab_inj p hg hb h1 (Prod.mk.inj h2).2)

theorem stepY_ok : ∀ {X : Fields} {n : ℕ} {SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n) (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q), X.Ok → ∀ (ST : Finset (HeightOneSpectrum (𝓞 X.E))) (pref : DecoF X.E n ST SG Q → Prop), (∀ b P, (Θ b P).H.FiniteIndex) → (∀ b P g, ∃ m : ℕ, 0 < m ∧ (Θ b P).lam g ^ m = 1) → (∀ N, Submodule.IsLattice X.E N → (y.ys N).Finite) → (stepY ST y β Λ Θ pref).Ok := by
  intro X n SG Q y β _ _ Λ Θ hX ST pref hfi hroot hfin
  have hG := fun b => FramedForms.main hX (ST := ST) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩) (Λ b) (Θ b) (hfi b)
    (levQ_root (Θ b) (hroot b))
  refine ⟨fun b => ?_, fun b p => ?_, fun b g => ?_, fun b g => ?_, fun b g p x => ?_, fun b p => ?_, fun b g p hg h1 => ?_⟩
  · letI := ptYAct (ST := ST) y (Λ b) (Θ b)
    haveI : Finite (MulAction.orbitRel.Quotient (FrmG (Λ b) (Θ b)) (DecoF X.E n ST SG Q)) := (hG b).fin_orb
    refine finite_orbits_of_finite_fibres (G := FrmG (Λ b) (Θ b)) (A := PtY ST SG Q y) (B := DecoF X.E n ST SG Q)
      (fun p => p.1.1) (fun _ _ => rfl) fun d => ?_
    refine Set.Finite.of_finite_image (f := fun p : PtY ST SG Q y => p.1.2) ?_ ?_
    · refine (hfin d.deco.1.N d.deco.2.1).subset ?_
      rintro _ ⟨p, hp, rfl⟩
      have hp' : p.1.1 = d := hp
      rw [← hp']
      exact p.2
    · intro p hp q hq h
      exact Subtype.ext (Prod.ext (hp.trans hq.symm) h)
  · letI := ptYAct (ST := ST) y (Λ b) (Θ b)
    haveI : Finite (MulAction.stabilizer (FrmG (Λ b) (Θ b)) p.1.1) := (hG b).fin_stab p.1.1
    refine Finite.of_injective (fun a : MulAction.stabilizer (FrmG (Λ b) (Θ b)) (show PtY ST SG Q y from p) =>
      (⟨a.1, congrArg (fun q : PtY ST SG Q y => q.1.1) a.2⟩ : MulAction.stabilizer (FrmG (Λ b) (Θ b)) p.1.1)) ?_
    intro a c h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  · exact ufGL_conjTranspose_mul g.1
  · obtain ⟨m, hm, hc⟩ := FramedForms.chr_root (Λ b) (Θ b) (levQ_root (Θ b) (hroot b)) g
    exact ⟨m, hm, Units.ext ((Units.val_pow_eq_pow_val _ _).trans hc)⟩
  · have h := p.1.1.deco.1.Lsh_act g.1.2 g.2.1.1
    show ((ufGL X.E n g.1 : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) *ᵥ x ∈ (p.1.1.deco.1.act g.1.1 g.2.1.1).Lsh ↔
      x ∈ p.1.1.deco.1.Lsh
    rw [h, ufGL_mulVec, mem_gmap, LinearEquiv.symm_apply_apply]
  · exact p.1.1.deco.2.Lsh_full_lattice
  · refine eq_one_of_fst (Λ b) (Θ b) p.1.1 g (congrArg (fun q : PtY ST SG Q y => q.1.1) hg) ?_
    have h2 : ufGL X.E n g.1 = 1 := h1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [← ufGL_mulVec, h2]
    simp

end GlobalTheory.Mem.Col2.StepOk
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.CovolTransport

section General

theorem isometry_iff {A : Type} [CommRing A] {M : ℕ} (s : A →+* A) (J g : Matrix (Fin M) (Fin M) A) :
    (∀ u w : Fin M → A, ∑ a, ∑ b, (g *ᵥ u) a * J b a * s ((g *ᵥ w) b) = ∑ a, ∑ b, u a * J b a * s (w b)) ↔
      Formalism.UG.cT s g * J * g = J := by
  have h1 : ∀ (K : Matrix (Fin M) (Fin M) A) (u w : Fin M → A),
      ∑ a, ∑ b, u a * K b a * s (w b) = (s ∘ w) ⬝ᵥ (K *ᵥ u) := by
    intro K u w
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : ∀ u w : Fin M → A, (s ∘ (g *ᵥ w)) ⬝ᵥ (J *ᵥ (g *ᵥ u)) =
      (s ∘ w) ⬝ᵥ ((Formalism.UG.cT s g * J * g) *ᵥ u) := by
    intro u w
    have e : s ∘ (g *ᵥ w) = g.map s *ᵥ (s ∘ w) := by
      funext a; exact RingHom.map_mulVec s g w a
    rw [e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
    rfl
  simp only [h1, h2]
  constructor
  · intro h
    ext a b
    have := h (Pi.single b 1) (Pi.single a 1)
    have e : s ∘ (Pi.single a 1 : Fin M → A) = Pi.single a 1 := by
      funext k
      by_cases hk : k = a <;> simp [Pi.single_apply, hk]
    rw [e] at this
    simpa using this
  · intro h u w
    rw [h]

variable {S : Type} [CommRing S] {I : Type} {M : ℕ} {e : S ≃+* (I → ℂ)} {θ : I → (S →+* ℂ)}

theorem ext_map (he : ∀ x i, e x i = θ i x) {X Y : Matrix (Fin M) (Fin M) S}
    (h : ∀ i, X.map (θ i) = Y.map (θ i)) : X = Y := by
  ext a b
  apply e.injective
  funext i
  rw [he, he]
  exact congrFun (congrFun (h i) a) b

theorem cT_map {s : S →+* S} {t : S →+* ℂ} (hs : ∀ x, t (s x) = star (t x))
    (X : Matrix (Fin M) (Fin M) S) :
    (Formalism.UG.cT s X).map t = Formalism.UG.cT (starRingEnd ℂ) (X.map t) := by
  ext a b
  simp [Formalism.UG.cT, hs]

theorem exists_equiv [TopologicalSpace S] (he : ∀ x i, e x i = θ i x) (hc : Continuous e)
    (hc' : Continuous e.symm) (s : S →+* S) (hs : ∀ x i, θ i (s x) = star (θ i x))
    (J : Matrix (Fin M) (Fin M) S) (H : Subgroup (I → GL (Fin M) ℂ))
    (hH : ∀ g, g ∈ H ↔ ∀ i, g i ∈ Formalism.UG.UJ (starRingEnd ℂ) (J.map (θ i))) :
    ∃ f : Formalism.UG.UJ s J ≃ₜ* H, ∀ h i, (((f h : I → GL (Fin M) ℂ) i : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) =
      ((h.1 : GL (Fin M) S) : Matrix (Fin M) (Fin M) S).map (θ i) := by
  have hone : ∀ i, (1 : Matrix (Fin M) (Fin M) S).map (θ i) = 1 := fun i =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have hθ : ∀ i, Continuous (θ i) := fun i => by
    have : (θ i : S → ℂ) = fun x => e x i := funext fun x => (he x i).symm
    rw [this]
    exact (continuous_apply i).comp hc
  let fw : Formalism.UG.UJ s J → H := fun h => ⟨fun i => Formalism.UG.bc (θ i) h.1, (hH _).2 fun i => by
    have hh : Formalism.UG.cT s h.1.1 * J * h.1.1 = J := h.2
    have h2 := congrArg (fun X => Matrix.map X (θ i)) hh
    simp only [Matrix.map_mul, cT_map (fun x => hs x i)] at h2
    exact h2⟩
  have hfw : ∀ h i, ((fw h).1 i).1 = h.1.1.map (θ i) := fun _ _ => rfl
  let L : H → Matrix (Fin M) (Fin M) S :=
    fun g => Matrix.of fun a b => e.symm fun i => (g.1 i).1 a b
  have hL : ∀ g i, (L g).map (θ i) = (g.1 i).1 := fun g i => by
    ext a b
    simp [L, ← he]
  have hLmul : ∀ g g', L g * L g' = L (g * g') := by
    intro g g'
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, hL, hL, hL]
    rfl
  have hL1 : L 1 = 1 := by
    refine ext_map he fun i => ?_
    rw [hL, hone]
    rfl
  have hLu : ∀ g, Formalism.UG.cT s (L g) * J * L g = J := by
    intro g
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (fun x => hs x i), hL]
    exact (hH _).1 g.2 i
  have hLc : Continuous L := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    refine hc'.comp (continuous_pi fun i => ?_)
    have : Continuous fun g : H => (g.1 i).1 :=
      Units.continuous_val.comp ((continuous_apply i).comp continuous_subtype_val)
    exact this.matrix_elem a b
  let bw : H → Formalism.UG.UJ s J := fun g =>
    ⟨⟨L g, L g⁻¹, by rw [hLmul, mul_inv_cancel, hL1], by rw [hLmul, inv_mul_cancel, hL1]⟩, hLu g⟩
  refine ⟨
    { toFun := fw
      invFun := bw
      left_inv := fun h => ?_
      right_inv := fun g => ?_
      map_mul' := fun h h' => ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun h i => rfl⟩
  · exact Subtype.ext (Units.ext (ext_map he fun i => hL (fw h) i))
  · exact Subtype.ext (funext fun i => Units.ext (hL g i))
  · exact Subtype.ext (funext fun i => map_mul (Formalism.UG.bc (θ i)) h.1 h'.1)
  · refine Continuous.subtype_mk (continuous_pi fun i => Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map (hθ i)
    · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map (hθ i)
  · exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨hLc, hLc.comp continuous_inv⟩) _

end General

theorem isCMFam_val {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    IsCMFam (fun τ : Ψ => τ.1) := by
  constructor
  · intro i j hij
    rcases InfinitePlace.mk_eq_iff.1 hij with h | h
    · exact Subtype.ext h
    · exact absurd (h ▸ j.2) ((hΨ _).1 i.2)
  · intro w
    by_cases h : w.embedding ∈ Ψ
    · exact ⟨⟨_, h⟩, w.mk_embedding⟩
    · have h' : ComplexEmbedding.conjugate w.embedding ∈ Ψ := by
        by_contra hn
        exact h ((hΨ _).2 hn)
      exact ⟨⟨_, h'⟩, (InfinitePlace.mk_conjugate_eq _).trans w.mk_embedding⟩

theorem finite_covolume_real_points : (∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), (∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ Ψ : Finset (E →+* ℂ), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ NumberField.ComplexEmbedding.conjugate τ ∉ Ψ) ∧ ∀ (H : Subgroup (Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ ∀ τ : Ψ, ∀ u w : Fin r → ℂ, ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) u) (Matrix.mulVec (g τ : Matrix (Fin r) (Fin r) ℂ) w) = ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G u w) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : MeasureTheory.Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, ReciprocityTheory.ChartRestriction.G.FD.IsUStab G Λ γ ∧ ∃ w ∈ Ω, ∀ τ : Ψ, (((g : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∀ ν : Measure (HA (Ainf F) σ J), ν.IsHaarMeasure → ∃ Ω : Set (HA (Ainf F) σ J), MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : HA (Ainf F) σ J, ∃ γ ∈ Formalism.UG.UJ (σ : E →+* E) J, (∀ x, x ∈ L ↔ (γ : Matrix (Fin M) (Fin M) E).mulVec x ∈ L) ∧ ∃ w ∈ Ω, HA.mat (Ainf F) σ J g = Formalism.UG.bc (inclR (F := F) (Ainf F)) γ * HA.mat (Ainf F) σ J w := by
  intro hyp F E _ _ _ _ _ σ hcm M J hJ L hL hsp ν hν
  haveI := hcm.1
  haveI := hcm.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = σ x := fun x => by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply φ.injective
    rw [ReciprocityTheory.ChartRestriction.G.FD.emb_cc, hcm.2.2.2]
    rfl
  obtain ⟨Ψ, hΨ, hcov⟩ := hyp E M Jᵀ L (fun a b => by rw [hcc]; exact hJ.1 a b)
    (by rw [Matrix.det_transpose]; exact hJ.2) hL hsp
  choose θ hθ using fun τ : Ψ => (GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E σ hcm τ.1).exists
  obtain ⟨e, he, hc, hc', hs⟩ :=
    GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ Ψ _ θ hcm (isCMFam_val Ψ hΨ) hθ
  have hincl : ∀ (X : Matrix (Fin M) (Fin M) E) (τ : Ψ),
      (X.map (inclR (F := F) (Ainf F))).map (θ τ) = X.map τ.1 := fun X τ => by
    ext a b
    exact (hθ τ).1 (X a b)
  let H : Subgroup (Ψ → GL (Fin M) ℂ) :=
    Subgroup.pi Set.univ fun τ => Formalism.UG.UJ (starRingEnd ℂ) (J.map τ.1)
  obtain ⟨f, hf⟩ : ∃ f : HA (Ainf F) σ J ≃ₜ* H, ∀ h i,
      (((f h : Ψ → GL (Fin M) ℂ) i : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) =
        (HA.mat (Ainf F) σ J h : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).map (θ i) :=
    exists_equiv he hc hc' (sigR (Ainf F) σ) (fun x i => by rw [← he, ← he, hs]) (JR (Ainf F) J) H
      fun g => by
        simp only [H, Subgroup.mem_pi, Set.mem_univ, forall_const, JR, hincl]
  borelize ↥H
  haveI : BorelSpace (HA (Ainf F) σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (Ainf F) σ J) :=
    f.toHomeomorph.isInducing.topologicalGroup f
  haveI : (ν.map f).IsHaarMeasure := f.isHaarMeasure_map ν
  obtain ⟨Ω, hΩm, hΩf, hΩ⟩ := hcov H (fun g => by
    simp only [H, Subgroup.mem_pi, Set.mem_univ, forall_const]
    exact forall_congr' fun τ => (isometry_iff (starRingEnd ℂ) (J.map τ.1) (g τ).1).symm) (ν.map f)
  have hfm : Measurable f := f.continuous.measurable
  refine ⟨f ⁻¹' Ω, hfm hΩm, by rwa [Measure.map_apply hfm hΩm] at hΩf, fun g => ?_⟩
  obtain ⟨γ, hγ, w, hw, hgw⟩ := hΩ (f g)
  refine ⟨γ, (isometry_iff (σ : E →+* E) J γ.1).1 fun u v => ?_, hγ.2, f.symm w, by simpa using hw, ?_⟩
  · have := hγ.1 u v
    simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, hcc, Matrix.transpose_apply] at this
    exact this
  · refine Units.ext (ext_map he fun τ => ?_)
    rw [Units.val_mul, Matrix.map_mul, ← hf, ← hf, f.apply_symm_apply, hgw, ← hincl]
    rfl

end GlobalTheory.Mem.CovolTransport
end
end

section

open Formalism.BasicNotions Formalism.IndefR MeasureTheory

namespace GlobalTheory.MinfMeasure

theorem exists_isMinf : ∀ p q : ℕ, ∃ m : Measure (UpqT p q), Lev.IsMinf m :=
  exists_isMinf_of_cd GlobalTheory.T.nonempty_compactDualHaar

end GlobalTheory.MinfMeasure
end
