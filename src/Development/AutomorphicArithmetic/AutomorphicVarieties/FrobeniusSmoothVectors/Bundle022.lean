module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle010
public import Mathlib.RingTheory.DualNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.RingTheory.Nakayama

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ep_rels :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (ι : Type) [Finite ι] (wt : ι → ZMod 2) (J : Ideal (MvPowerSeries ι O)), IsHomog O wt J → ∃ (κ : Type) (_ : Fintype κ) (f : κ → MvPowerSeries ι O) (wf : κ → ZMod 2), (∀ u, f u ∈ wtPart O wt (wf u)) ∧ J = Ideal.span (Set.range f) ∧ ∀ c : κ → O, ∑ u, c u • f u ∈ maximalIdeal (MvPowerSeries ι O) * J → ∀ u, c u ∈ maximalIdeal O := by
  intro O _ _ _ _ h2 ι _ wt J hJ
  haveI : IsCO O (MvPowerSeries ι O) := co_mvps O O ι
  obtain ⟨τ, hττ, hev, hw⟩ := ep_ps O h2 ι wt
  have hτJ : ∀ y ∈ J, τ y ∈ J := by
    intro y hy
    have e := hw 1 y
    have hs : sg (MvPowerSeries ι O) 1 = -1 := by
      simp only [sg]
      rw [show ZMod.val (1 : ZMod 2) = 1 from rfl, pow_one]
    rw [hs] at e
    have : τ y = y - 2 * wcomp O wt 1 y := by linear_combination e
    rw [this]
    exact J.sub_mem hy (J.mul_mem_left 2 (hJ y hy 1))
  have hτm : ∀ y ∈ maximalIdeal (MvPowerSeries ι O), τ y ∈ maximalIdeal (MvPowerSeries ι O) := by
    intro y hy
    rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro hu
    apply hy
    rw [← hττ y]
    exact hu.map τ
  have hτN : ∀ y ∈ maximalIdeal (MvPowerSeries ι O) * J,
      τ y ∈ maximalIdeal (MvPowerSeries ι O) * J := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro m hm j hj
      rw [map_mul]
      exact Ideal.mul_mem_mul (hτm m hm) (hτJ j hj)
    · intro a b ha hb
      rw [map_add (f := _)]
      exact Ideal.add_mem _ ha hb
  obtain ⟨a, g, z, hz, hle, hmin⟩ :=
    ep_basis O h2 (MvPowerSeries ι O) τ hττ J (maximalIdeal (MvPowerSeries ι O) * J) hτJ hτN le_rfl
  refine ⟨Fin a ⊕ Fin g, inferInstance, z, Space.Loc.par a g, ?_, ?_, hmin⟩
  · intro s
    rw [← hev]
    exact (hz s).2
  · apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian J)
        (maximalIdeal_le_jacobson _)
      exact hle
    · rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      exact (hz s).1
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] {C' : Type} [CommRing C'] [Algebra O C'] [IsCO O C']
  {C'' : Type} [CommRing C''] [Algebra O C''] [IsCO O C'']

private theorem mem_max_iff (q : C' →ₐ[O] C'') (x : C') : q x ∈ maximalIdeal C'' ↔ x ∈ maximalIdeal C' := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem adicCont_map {Γ : Type} [TopologicalSpace Γ] (q : C' →ₐ[O] C'') {f : Γ → C'}
    (hf : AdicCont (maximalIdeal C') f) : AdicCont (maximalIdeal C'') fun g => q (f g) := by
  intro N
  have hle : maximalIdeal C' ^ N ≤ (maximalIdeal C'' ^ N).comap (q : C' →+* C'') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    exact (mem_max_iff q y).2 hy
  exact (hf N).comp (Ideal.quotientMap _ (q : C' →+* C'') hle)

private theorem map_sgnAct {m : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (s : ℤˣ)
    (g : GL (Fin m) A) :
    GeneralLinearGroup.map f (sgnAct m A s g) = sgnAct m A' s (GeneralLinearGroup.map f g) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one, sgnAct_one]
  · rw [sgnAct_neg_one, sgnAct_neg_one, map_theta]

private theorem val_sub_one_map {m : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A')
    (g : GL (Fin m) A) (i j : Fin m) :
    (((GeneralLinearGroup.map f g : GL (Fin m) A') : Matrix (Fin m) (Fin m) A') - 1) i j =
      f (((g : Matrix (Fin m) (Fin m) A) - 1) i j) := by
  have e : ((GeneralLinearGroup.map f g : GL (Fin m) A') : Matrix (Fin m) (Fin m) A') - 1 =
      f.mapMatrix ((g : Matrix (Fin m) (Fin m) A) - 1) := by
    rw [map_sub, map_one]
    rfl
  rw [e]
  rfl

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
  {R : Type} [CommRing R] [Algebra O R] {B : Box F n R}

private noncomputable def push (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R) (D : SetLift (p''.comp q) B) :
    SetLift p'' B where
  r s := GeneralLinearGroup.map (q : C' →+* C'') (D.r s)
  r_cont i j := adicCont_map q (D.r_cont i j)
  r_map s := D.r_map s
  g v := GeneralLinearGroup.map (q : C' →+* C'') (D.g v)
  g_map v := D.g_map v
  t v s := GeneralLinearGroup.map (q : C' →+* C'') (D.t v s)
  t_cont v i j := adicCont_map q (D.t_cont v i j)
  t_tri v s i j h := (congrArg q (D.t_tri v s i j h)).trans (map_zero q)
  t_map v s := D.t_map v s

private theorem push_om (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R) (D : SetLift (p''.comp q) B)
    (x : F.Γ × F.Γ) (i j : Fin n) : (push q p'' D).om x i j = q (D.om x i j) := by
  refine Eq.trans ?_ (val_sub_one_map (q : C' →+* C'') _ i j)
  rw [map_mul, map_mul, map_inv, map_sgnAct]
  rfl

private theorem push_a (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R) (D : SetLift (p''.comp q) B)
    (v : F.V) (s : F.Gv v) (i j : Fin n) : (push q p'' D).a v s i j = q (D.a v s i j) := by
  refine Eq.trans ?_ (val_sub_one_map (q : C' →+* C'') _ i j)
  rw [map_mul, map_inv, map_mul, map_mul, map_inv]
  rfl

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.pr_obs :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (p : C' →ₐ[O] R) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → D.co u ∈ continuousCoboundaries2 F.loc (B.bar O).ad (B.bar O).b → ∀ (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R), p''.comp q = p → Function.Surjective q → (∀ y : RingHom.ker p, u y = 0 → q y = 0) → ∃ s : R →ₐ[O] C'', p''.comp s = AlgHom.id O R := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ ρ B hU hOf hC hG C' _ _ _ p D u hsm hco C'' _ _ _ q p'' hpq hq hu
  subst hpq
  have hK : RingHom.ker (p''.comp q) ≤ maximalIdeal C' := fun y hy => by
    rw [← mem_max_iff (p''.comp q), (RingHom.mem_ker).1 hy]
    exact zero_mem _
  obtain ⟨μ, hμ, hμu, hμq⟩ := pr_mu O C' C'' _ q u hsm hK hq hu
  obtain ⟨hom, ha, -, -⟩ := pr_omk hF O C' R (p''.comp q) B D hsm
  obtain ⟨β, Y, hβ, h1, h2⟩ := hco
  have hev : ∀ y ∈ RingHom.ker (p''.comp q), q y = μ (evK _ u y) := fun y hy => by
    rw [evK_of_mem u hy, hμu]
  have hp0 : ∀ c, p'' (μ c) = 0 := fun c => by
    obtain ⟨y, hy⟩ := hμq c
    rw [hy]
    exact y.2
  obtain ⟨B', hB'c, hB'm, -⟩ := pr_correct hF O C'' R p'' B (push q p'' D) μ hμ hp0 β Y (D.co u).2 hβ
    (fun x => by
      rw [← h1]
      ext i j
      rw [push_om, hev _ (hom x i j)]
      rfl)
    (fun v s => by
      ext i j
      rw [push_a, hev _ (ha v s i j)]
      rfl) h2
  have hsm'' : maximalIdeal C'' * RingHom.ker p'' = ⊥ := by
    refine le_bot_iff.1 (Ideal.mul_le.2 fun a ha' b hb => ?_)
    obtain ⟨a, rfl⟩ := hq a
    obtain ⟨b, rfl⟩ := hq b
    have hab : a * b ∈ maximalIdeal C' * RingHom.ker (p''.comp q) :=
      Ideal.mul_mem_mul ((mem_max_iff q a).1 ha') hb
    rw [hsm, Ideal.mem_bot] at hab
    rw [← map_mul, hab, map_zero]
    exact zero_mem _
  obtain ⟨-, ρ', -, hρm, hρc, -, -⟩ := pr_norm hF O C'' R p'' ρ B' hsm'' hG (hB'm ▸ hOf) hB'c
  have hbar : ρ'.bar O = ρ.bar O := by
    have e : (res O C'' : C'' →+* ResidueField O) =
        (res O R : R →+* ResidueField O).comp (p'' : C'' →+* R) :=
      RingHom.ext fun x => (res_map p'' x).symm
    show ρ'.map _ = ρ.map _
    rw [e, ← NRep.map_map, hρm]
  obtain ⟨g, hg, -⟩ := hU.univ C'' ρ' hρc hbar
  obtain ⟨g', -, hg'⟩ := hU.univ R ρ hU.cont rfl
  refine ⟨g, (hg' _ ?_).trans (hg' _ rfl).symm⟩
  show ρ.map ((p'' : C'' →+* R).comp (g : R →+* C'')) = ρ
  rw [← NRep.map_map, hg, hρm]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_tbox :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ [IsCO O (ResidueField O)] [IsCO O (DualNumber (ResidueField O))] (B : Box F n (ResidueField O)), (IsLocallyConstant fun s => (B.r s).mat) → ∀ x ∈ Z1C F.loc B.ad B.b, ∃ B' : Box F n (DualNumber (ResidueField O)), B'.Cont (maximalIdeal _) ∧ B'.map (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O) : (DualNumber (ResidueField O)) →+* ResidueField O) = B ∧ ∀ s, (B'.r s).mat.map TrivSqZeroExt.snd = x.1 s * (B.r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ _ _ B hB x hx
  have hres : ∀ y : ResidueField O, res O (ResidueField O) y = y := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    have h := (res O (ResidueField O)).commutes a
    rw [IsLocalRing.ResidueField.algebraMap_eq] at h
    exact h
  have hbar : Box.bar O B = B := by
    apply Box.ext
    · ext s
      · simp [Box.bar, Box.map, GG.map, hres]
      · simp [Box.bar, Box.map, GG.map]
    · funext v
      ext i j
      simp [Box.bar, Box.map, hres]
  let ι : ResidueField O →+* DualNumber (ResidueField O) := algebraMap _ _
  let p := TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)
  have hp : ∀ X : GL (Fin n) (ResidueField O), GeneralLinearGroup.map (p : DualNumber (ResidueField O) →+* ResidueField O) (GeneralLinearGroup.map ι X) = X := by
    intro X
    ext i j
    simp [p, ι, TrivSqZeroExt.algebraMap_eq_inl]
  have hloc : ∀ v, Continuous (F.loc v) := by
    intro v
    exact continuous_subtype_val.comp (hF.loc_cont v)
  have hlc : ∀ (f : Matrix (Fin n) (Fin n) (ResidueField O) → DualNumber (ResidueField O)) (N : ℕ),
      IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal (DualNumber (ResidueField O)) ^ N) (f (B.r s).mat) :=
    fun f N => hB.comp (fun M => Ideal.Quotient.mk _ (f M))
  let D : SetLift p B :=
    { r := fun s => GeneralLinearGroup.map ι (B.r s).left
      r_cont := fun i j N => hlc (fun M => ι (M i j)) N
      r_map := fun s => hp _
      g := fun v => GeneralLinearGroup.map ι (B.g v)
      g_map := fun v => hp _
      t := fun v s => GeneralLinearGroup.map ι (B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹)
      t_cont := by
        intro v i j N
        have h := (hlc (fun M => ι (((B.g v).val * M * (B.g v)⁻¹.val) i j)) N).comp_continuous (hloc v)
        exact h
      t_tri := by
        intro v s i j hij
        have h := congrArg ι (B.tri v s i j hij)
        rw [map_zero] at h
        exact h
      t_map := fun v s => hp _ }
  let μ : ResidueField O →+ DualNumber (ResidueField O) :=
    (TrivSqZeroExt.inrHom (ResidueField O) (ResidueField O)).toAddMonoidHom
  have hresD : ∀ a : DualNumber (ResidueField O), res O (DualNumber (ResidueField O)) a = a.fst := by
    intro a
    rw [← res_map p a, hres]
    rfl
  have hμ : IsSq O μ := by
    constructor
    · intro a c
      rw [hresD]
      ext
      · simp [μ]
      · show (TrivSqZeroExt.inr (a.fst * c) : DualNumber (ResidueField O)).snd = (a * TrivSqZeroExt.inr c).snd
        rw [TrivSqZeroExt.snd_mul]
        simp only [TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, MulOpposite.op_zero, zero_smul, add_zero, smul_eq_mul]
    · intro c
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map p
      simp [p, μ] at this
  have hR : ∀ s t : F.Γ, GeneralLinearGroup.map ι (B.r (s * t)).left =
      GeneralLinearGroup.map ι (B.r s).left * sgnAct n _ (F.del s) (GeneralLinearGroup.map ι (B.r t).left) := by
    intro s t
    have h1 := congrArg SemidirectProduct.left (map_mul ((GG.map ι).comp B.r) s t)
    have h2 : (((GG.map ι).comp B.r) s).right = F.del s := B.nu s
    rw [SemidirectProduct.mul_left, h2] at h1
    exact h1
  refine (pr_correct hF O _ _ p B D μ hμ (fun c => by simp [p, μ]) (fun s => -x.1 s) (fun v => -x.2 v)
    (fun _ _ => 0) ?g1 ?g2 ?g3 ?g4).imp fun B' h => ⟨h.1, h.2.1, fun s => ?g5⟩
  case g5 =>
    rw [h.2.2 s]
    ext i j
    show (((1 - (-x.1 s).map μ) * ((B.r s).left.val.map ι) : Matrix (Fin n) (Fin n) (DualNumber (ResidueField O))) i j).snd = _
    rw [Matrix.mul_apply, TrivSqZeroExt.snd_sum, GG.mat, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [TrivSqZeroExt.snd_mul]
    simp [Matrix.one_apply, μ, ι, TrivSqZeroExt.algebraMap_eq_inl, op_smul_eq_mul]
    left
    split_ifs <;> simp
  case g1 => exact hx.1.comp (fun M => -M)
  case g2 =>
    intro y
    rw [hbar]
    have hc := hx.2.1 y.1 y.2
    have h0 : dOne B.ad (fun s => -x.1 s) y = 0 := by
      simp only [dOne, map_neg, hc]
      abel
    rw [h0, Matrix.map_zero _ (map_zero μ)]
    show (GeneralLinearGroup.map ι (B.r y.1).left * sgnAct n _ (F.del y.1) (GeneralLinearGroup.map ι (B.r y.2).left) *
      (GeneralLinearGroup.map ι (B.r (y.1 * y.2)).left)⁻¹).val - 1 = 0
    rw [hR, mul_inv_cancel, Units.val_one, sub_self]
  case g3 =>
    intro v s
    rw [Matrix.map_zero _ (map_zero μ)]
    show (GeneralLinearGroup.map ι (B.r (F.loc v s)).left * ((GeneralLinearGroup.map ι (B.g v))⁻¹ *
      GeneralLinearGroup.map ι (B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹) * GeneralLinearGroup.map ι (B.g v))⁻¹).val - 1 = 0
    simp [map_mul, map_inv, mul_assoc]
  case g4 =>
    intro v s
    rw [hbar]
    have h := hx.2.2 v s
    convert h using 1
    simp only [map_neg]
    abel
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_limit :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D) (ρ : NRep F n D), IsVertexRing C 𝔪 → IsModel O C 𝔪 ρ → ∃ (ξ : S.A →ₐ[O] D) (β : S.B →ₐ[O] C), S.u.map (ξ : S.A →+* D) = ρ ∧ ∀ b, ξ (S.inc b) = algebraMap C D (β b) := by
  intro l _ O _ _ F n S C _ _ _ D _ _ _ _ 𝔪 ρ hV hM
  obtain ⟨f, hf1, hf2, hf3⟩ := alg_family S C 𝔪 ρ hV hM
  haveI : IsAdicComplete (maximalIdeal C) C := IsCO.complete (O := O)
  have hsep : ∀ d d' : D, (∀ N : ℕ, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = Ideal.Quotient.mk (𝔪 ^ (N + 1)) d') → d = d' := by
    intro d d' h
    have hmem : d - d' ∈ ⨅ N, 𝔪 ^ N := by
      refine (Submodule.mem_iInf _).2 fun N => ?_
      cases N with
      | zero => simp
      | succ N => exact Ideal.Quotient.eq.1 (h N)
    rw [hV.sep] at hmem
    exact sub_eq_zero.1 ((Submodule.mem_bot _).1 hmem)
  have hr : ∀ N g i j, f N (S.ρ.r g i j) = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ρ.r g i j) := by
    intro N g i j
    have := congrArg (fun σ => σ.r g i j) (hf1 N)
    simpa only [NRep.map_r, AlgHom.coe_toRingHom] using this
  have hψ : ∀ N v i g, f N ((S.ρ.ψ v i g : S.R)) = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ρ.ψ v i g : D) := by
    intro N v i g
    have := congrArg (fun σ => ((σ.ψ v i g : Units _) : D ⧸ 𝔪 ^ (N + 1))) (hf1 N)
    simpa only [NRep.map_ψ, AlgHom.coe_toRingHom] using this
  let T' : Subalgebra O S.R :=
    { carrier := {x | ∃ c : C, ∀ N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D c) = f N x}
      mul_mem' := by
        rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c * c', fun N => by simp only [map_mul, hc, hc']⟩
      add_mem' := by
        rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c + c', fun N => by simp only [map_add (f := _), hc, hc']⟩
      algebraMap_mem' := fun a => ⟨algebraMap O C a, fun N => by
        rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
        rfl⟩ }
  let T : Subalgebra O S.R :=
    { carrier := {x | ∃ d : D, ∀ N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = f N x}
      mul_mem' := by
        rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c * c', fun N => by simp only [map_mul, hc, hc']⟩
      add_mem' := by
        rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c + c', fun N => by simp only [map_add (f := _), hc, hc']⟩
      algebraMap_mem' := fun a => ⟨algebraMap O D a, fun N => by
        rw [AlgHom.commutes]
        rfl⟩ }
  have hgen : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = ↑((S.ρ.ψ v i) g)}) ≤ T' := by
    refine Algebra.adjoin_le ?_
    rintro x (hx | ⟨v, i, g, rfl⟩)
    · obtain ⟨L, hL, rfl⟩ := hx
      obtain ⟨c, hc⟩ := hM.mon _ ⟨L, hL, rfl⟩
      refine ⟨c, fun N => ?_⟩
      rw [hc, map_list_prod, map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left ?_
      intro s _
      simp only [Function.comp, hr]
    · obtain ⟨c, hc, -⟩ := hM.psi v i g
      exact ⟨c, fun N => by rw [hc, hψ]⟩
  have hB : S.B ≤ T' := by
    intro x hx
    have hx' : ∀ N : ℕ, ∃ y ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = ↑((S.ρ.ψ v i) g)}), x - y ∈ maximalIdeal S.R ^ N := hx
    choose y hy hxy using hx'
    choose c hc using fun N => hgen (hy (N + 1))
    have hfx : ∀ N M, N + 1 ≤ M → f N x = f N (y M) := by
      intro N M hNM
      have h0 := hf3 N _ (Ideal.pow_le_pow_right hNM (hxy M))
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    have hcau : ∀ N : ℕ, algebraMap C D (c (N + 1) - c N) ∈ 𝔪 ^ (N + 1) := by
      intro N
      rw [map_sub]
      refine Ideal.Quotient.eq.1 ?_
      rw [hc, hc, ← hfx N (N + 1 + 1) (by omega), ← hfx N (N + 1) le_rfl]
    obtain ⟨z, hz⟩ := alg_closed C 𝔪 hV c hcau
    refine ⟨z, fun N => ?_⟩
    have h1 : Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D z) = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D (c N)) := by
      refine Ideal.Quotient.eq.2 ?_
      rw [← map_sub]
      exact hz N
    rw [h1, hc, ← hfx N (N + 1) le_rfl]
  have hA : S.A ≤ T := by
    show Algebra.adjoin O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j}) ≤ T
    refine Algebra.adjoin_le ?_
    rintro x (hx | ⟨g, i, j, rfl⟩)
    · obtain ⟨c, hc⟩ := hB hx
      exact ⟨algebraMap C D c, hc⟩
    · exact ⟨ρ.r g i j, fun N => (hr N g i j).symm⟩
  obtain ⟨ξ, hξ⟩ := alg_glue (A := S.A) 𝔪 hV.sep (fun N => (f N).comp S.A.val) (fun a => by
    obtain ⟨d, hd⟩ := hA a.2
    exact ⟨d, fun N => by simpa using hd N⟩)
  have hξ' : ∀ (a : S.A) N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ξ a) = f N (a : S.R) := by
    intro a N
    simpa using hξ a N
  let φ := IsScalarTower.toAlgHom O C D
  have hmem : ∀ b, (ξ.comp S.inc) b ∈ φ.range := by
    intro b
    obtain ⟨c, hc⟩ := hB b.2
    refine (AlgHom.mem_range φ).2 ⟨c, ?_⟩
    refine hsep _ _ fun N => ?_
    show Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D c) = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ξ (S.inc b))
    rw [hc, hξ']
    rfl
  let e := AlgEquiv.ofInjective φ hV.inj
  refine ⟨ξ, e.symm.toAlgHom.comp ((ξ.comp S.inc).codRestrict φ.range hmem), ?_, ?_⟩
  · refine NRep.ext ?_ ?_
    · refine MonoidHom.ext fun g => Matrix.ext fun i j => ?_
      rw [NRep.map_r]
      refine hsep _ _ fun N => ?_
      rw [← hr]
      exact hξ' _ N
    · funext v i
      refine MonoidHom.ext fun g => Units.ext ?_
      rw [NRep.map_ψ]
      refine hsep _ _ fun N => ?_
      rw [← hψ]
      exact hξ' _ N
  · intro b
    have h1 : ((e (e.symm ⟨ξ (S.inc b), hmem b⟩) : φ.range) : D) = φ (e.symm ⟨ξ (S.inc b), hmem b⟩) :=
      AlgEquiv.ofInjective_apply _ _ _
    rw [AlgEquiv.apply_symm_apply] at h1
    exact h1
end
