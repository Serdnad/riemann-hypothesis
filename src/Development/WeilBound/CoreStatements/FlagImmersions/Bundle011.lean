module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LowerBoundOfBaseSetting
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle013
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifRiem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle090
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleGeneric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle016
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MultiIsProjVarFOfRatDiv
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem geoNum_zero_nonneg' {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 W a := by
  rw [geoNum]
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem geoNum_one_nonneg' {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (a : K → ℤ) (ha : ∀ k, 0 ≤ a k) : 0 ≤ geoNum 1 W (fun _ => a) := by
  rw [geoNum]
  split_ifs
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (ha k) ?_
    refine finsum_nonneg fun V => finsum_nonneg fun _ => ?_
    exact mul_nonneg (Int.natCast_nonneg _) (geoNum_zero_nonneg' _ _)
  · exact le_rfl

end RootFieldNumerics

theorem RootFieldNumerics.root_model_nef_fibres_base : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N), (∀ k, 0 ≤ M.A.a k) → M.NefFib 0 1 := by
  intro Ψ _ N M hA p _ W _
  unfold GlobalTheory.CompanionTheory.Ar.Top.RootModel.curveDeg
  refine Finset.sum_nonneg fun j _ => ?_
  rcases j with _ | r
  · have hk : (0:ℝ) < M.kA := by exact_mod_cast M.kA_pos
    have hg := RootFieldNumerics.geoNum_one_nonneg' W M.A.a hA
    simp only [GlobalTheory.CompanionTheory.Ar.Top.RootModel.coef, GlobalTheory.CompanionTheory.Ar.Top.RootModel.line]
    exact mul_nonneg (by positivity) (by exact_mod_cast hg)
  · simp [GlobalTheory.CompanionTheory.Ar.Top.RootModel.coef]
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.HH

theorem exists_word {J : Type} : ∀ (d : ℕ) (m : J →₀ ℕ), m.degree = d →
    ∃ w : Fin d → J, m = ∑ k, Finsupp.single (w k) 1 := by
  intro d
  induction d with
  | zero =>
    intro m hm
    refine ⟨Fin.elim0, ?_⟩
    rw [(Finsupp.degree_eq_zero_iff m).1 hm]
    simp
  | succ d ih =>
    intro m hm
    have hne : m ≠ 0 := by
      rintro rfl
      simp at hm
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hne
    have hle : Finsupp.single j 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hj
      omega
    have hsplit : m = Finsupp.single j 1 + (m - Finsupp.single j 1) :=
      (add_tsub_cancel_of_le hle).symm
    have hdeg : Finsupp.degree (m - Finsupp.single j 1) = d := by
      have h2 := congrArg Finsupp.degree hsplit
      rw [map_add (f := _), Finsupp.degree_single, hm] at h2
      omega
    obtain ⟨w', hw'⟩ := ih _ hdeg
    refine ⟨Fin.cons j w', ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hw']
    exact hsplit

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem hhFl_word (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    (hP : IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1))
    (w : Fin (dimFl Ψ N + 1) → Ψ × Fin N) (c : ℝ) :
    hhFl Ψ N II (monomial (∑ k, Finsupp.single (w k) 1) c) = c * ((-1) ^ (dimFl Ψ N + 1) *
      II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
        (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w k))) := by
  have hdeg : (∑ i, Finsupp.single (w i) (1 : ℕ)).degree = dimFl Ψ N + 1 := by

    rw [map_sum]
    simp [Finsupp.degree_single]
  rw [HhModel.hhFl_monomial, hdeg]
  congr 2
  exact GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.hFlMono_sum_single Ψ N II hII hP w

end RootFieldNumerics.HH
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem abel_le {N : ℕ} (f u : Fin (N + 1) → ℝ) (hf : ∀ a b, a ≤ b → f b ≤ f a)
    (hu : ∀ i, 0 ≤ ∑ k ∈ Finset.Iic i, u k) (i : Fin (N + 1)) :
    f i * ∑ k ∈ Finset.Iic i, u k ≤ ∑ k ∈ Finset.Iic i, f k * u k := by
  induction i using Fin.induction with
  | zero =>
    have : Finset.Iic (0 : Fin (N + 1)) = {0} := by ext k; simp
    simp [this]
  | succ j ih =>
    have h1 : Finset.Iic j.succ = insert j.succ (Finset.Iic j.castSucc) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
      omega
    have h2 : j.succ ∉ Finset.Iic j.castSucc := by
      simp only [Finset.mem_Iic, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      omega
    rw [h1, Finset.sum_insert h2, Finset.sum_insert h2]
    have h3 := hf j.castSucc j.succ (Fin.castSucc_lt_succ).le
    have h4 := mul_le_mul_of_nonneg_right h3 (hu j.castSucc)
    rw [mul_add]
    linarith

theorem abel_nonneg {N : ℕ} (f u : Fin N → ℝ) (hf : ∀ a b, a ≤ b → f b ≤ f a)
    (hu : ∀ i, 0 ≤ ∑ k ∈ Finset.Iic i, u k)
    (h0 : ∀ i : Fin N, (i : ℕ) + 1 = N → ∑ k ∈ Finset.Iic i, u k = 0) : 0 ≤ ∑ k, f k * u k := by
  obtain _ | N := N
  · simp
  · have h := abel_le f u hf hu (Fin.last N)
    rw [h0 (Fin.last N) (by simp), mul_zero] at h
    have e : Finset.Iic (Fin.last N) = Finset.univ := by
      ext k; simp [Fin.le_last]
    rwa [e] at h

theorem tower_nef_generic_dominant : PB.NefPol → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.Smooth → R.Flat → ∀ B c, (∀ lam : Wt Ψ N, Dominant lam → (T.M B c).NefGen lam 0) ∧ (T.M B c).NefGen 0 1 := by
  intro hNP hI II _ Ψ _ _ N T R hSm hFl B c
  classical
  obtain ⟨hJ, alg, -⟩ := hSm B c
  set M := T.M B c with hM
  revert hJ
  generalize R.tie B c = tie
  intro hJ
  have : CharZero M.Ω := algebraRat.charZero M.Ω
  let I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily ℚ M.ι := fun V _ L => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ V L
  have hIf : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I :=
    GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full _ _ _
  let Fl : Set (Option (Ψ × Fin N)) := {a | ∃ τ, ∃ i : Fin N, (i : ℕ) + 1 = N ∧ a = some (τ, i)}
  have hnef := fun n hn => (hNP hI (dimFl Ψ N) (Option (Ψ × Fin N)) (R.Sys c) Fl
    (by rintro _ ⟨τ, i, hi, rfl⟩ t; exact hFl c τ i hi t) M.K M.ι M.Ω M.y tie.Re hJ M.birational I hIf n hn).1
  have key : ∀ W : Ideal (MRing M.ι), IsArithVar W 2 → M.P ≤ W → ∃ d : (M.K → ℤ) →+ ℤ,
      (∀ L : HermLine M.ι, IsSmoothHerm L → geomDeg W L 1 = d L.a) ∧ (∀ a, 0 ≤ d (tie.Re.ref a).a) ∧
        ∀ a ∈ Fl, d (tie.Re.ref a).a = 0 := by
    intro W hW hPW
    have hWq : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 :=
      GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW
    have hup : ∀ a : M.K → ℤ, Function.update (fun _ : Fin 1 => (0 : M.K → ℤ)) 0 a = fun _ => a := by
      intro a; funext j; rw [Subsingleton.elim j 0]; simp
    let d : (M.K → ℤ) →+ ℤ := AddMonoidHom.mk'
      (fun a => I (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 fun _ => a) fun a b => by
        have := ReciprocityTheory.ChartRestriction.G.AI.I1.multilin_thm ℚ M.ι I hIf _ 1 (fun _ => 0) 0 a b hWq
        simpa only [hup] using this
    have hpos : ∀ n : Option (Ψ × Fin N) → ℤ, (∀ a ∉ Fl, 0 ≤ n a) → 0 ≤ d (PB.combLine tie.Re.ref n).a := by
      intro n hn
      have := hnef n hn _ hWq (Ideal.map_mono hPW)
      have e : ![(PB.combLine tie.Re.ref n).a] = fun _ : Fin 1 => (PB.combLine tie.Re.ref n).a := by
        funext j; rw [Subsingleton.elim j 0]; rfl
      rw [e] at this
      exact this
    have hs : ∀ (a : Option (Ψ × Fin N)) (m : ℤ),
        (PB.combLine tie.Re.ref (Pi.single a m)).a = m • (tie.Re.ref a).a := by
      intro a m
      funext k
      rw [PB.combLine_a, Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      simp
    have h1 : ∀ a, 0 ≤ d (tie.Re.ref a).a := by
      intro a
      have := hpos (Pi.single a 1) fun b _ => by
        by_cases hb : b = a
        · simp [hb]
        · simp [Pi.single_eq_of_ne hb]
      rwa [hs, one_smul] at this
    refine ⟨d, fun L hL => ?_, h1, fun a ha => ?_⟩
    · exact Giv.degreeGeneric_of_degree hI.degree M.K M.ι W 1 (fun _ => L) hW fun _ => hL
    · have := hpos (Pi.single a (-1)) fun b hbF => by
        have hb : b ≠ a := fun h => hbF (h ▸ ha)
        simp [Pi.single_eq_of_ne hb]
      rw [hs, neg_one_smul, map_neg] at this
      linarith [h1 a]
  refine ⟨fun lam hlam W hW hPW => ?_, fun W hW hPW => ?_⟩
  · obtain ⟨d, hd, h1, h0⟩ := key W hW hPW
    have hS : ∀ τ i, ∑ k ∈ Finset.Iic i, (-(d (M.xdeg (τ, k)) : ℝ)) = d (tie.Re.ref (some (τ, i))).a := by
      intro τ i

      rw [tie.fund_deg, map_neg, map_sum]
      simp
      rfl
    rw [Fintype.sum_option, Fintype.sum_prod_type]
    have e0 : M.coef lam 0 none = 0 := by simp [RootModel.coef]
    rw [e0, zero_mul, zero_add]
    refine Finset.sum_nonneg fun τ _ => ?_
    have := abel_nonneg (lam τ) (fun k => -(d (M.xdeg (τ, k)) : ℝ)) (hlam τ)
      (fun i => by rw [hS]; exact_mod_cast h1 _)
      (fun i hi => by rw [hS, h0 _ ⟨τ, i, hi, rfl⟩]; simp)
    refine this.trans_eq (Finset.sum_congr rfl fun k _ => ?_)
    have e1 : geomDeg W (M.line 1 (some (τ, k))) 1 = d (M.xdeg (τ, k)) := by
      rw [← M.x_deg 1 (τ, k)]
      exact hd _ (M.x_smooth 1 _)
    rw [e1]
    simp [RootModel.coef]
  · obtain ⟨d, hd, h1, -⟩ := key W hW hPW
    rw [Fintype.sum_option]
    have e0 : ∀ r, M.coef (0 : Wt Ψ N) 1 (some r) = 0 := fun r => by simp [RootModel.coef]
    simp only [e0, zero_mul, Finset.sum_const_zero, add_zero]
    have e1 : geomDeg W (M.line 1 none) 1 = d (tie.Re.ref none).a := by
      rw [tie.ref_none.1]
      exact hd _ M.A_smooth
    rw [e1]
    refine mul_nonneg ?_ (by exact_mod_cast h1 _)
    simp [RootModel.coef]

end RootFieldNumerics
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace RootFieldNumerics.PC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem mem_eig {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : 𝓞 E →+* Module.End ℂ V} {s : 𝓞 E →+* ℂ} {x : V} :
    x ∈ eigSp ρ s ↔ ∀ a, ρ a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem ip_sum (R : RiemLat E g Λ) {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → ℂ) (c : κ → ℂ) (u : ι → Fin g → ℂ)
    (w : κ → Fin g → ℂ) :
    R.ip (∑ k, a k • u k) (∑ l, c l • w l) = ∑ k, ∑ l, star (a k) * c l * R.ip (u k) (w l) := by
  simp only [RiemLat.ip, star_sum, star_smul, mulVec_sum, mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem ip_conj (R : RiemLat E g Λ) (x y : Fin g → ℂ) : (starRingEnd ℂ) (R.ip x y) = R.ip y x :=
  conj_hermForm R.herm y x

theorem ip_zero_left (R : RiemLat E g Λ) (y : Fin g → ℂ) : R.ip 0 y = 0 := by simp [RiemLat.ip]

theorem ip_zero_right (R : RiemLat E g Λ) (y : Fin g → ℂ) : R.ip y 0 = 0 := by simp [RiemLat.ip]

theorem exists_onb (R : RiemLat E g Λ) (W : Submodule ℂ (Fin g → ℂ)) {m : ℕ} (hm : Module.finrank ℂ W = m) :
    ∃ e : Fin m → Fin g → ℂ, (∀ i, e i ∈ W) ∧ (∀ i j, R.ip (e i) (e j) = if i = j then 1 else 0) ∧
      ∀ z ∈ W, ∃ α : Fin m → ℂ, z = ∑ i, α i • e i := by
  classical
  obtain ⟨c, hc⟩ := GlobalTheory.T.hermitian_restriction_orthonormal_coords g m R.Hm R.herm R.pos W hm
  have hinj : Function.Injective (c.comp W.subtype) := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    by_contra h0
    have h1 := R.pos z fun h => h0 (Subtype.ext h)
    have hz' : c z = 0 := hz
    rw [hc z z.2 z z.2, hz'] at h1
    simp at h1
  have hsur : Function.Surjective (c.comp W.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hm])).1 hinj
  choose e he using fun i => hsur (Pi.single i 1)
  refine ⟨fun i => e i, fun i => (e i).2, fun i j => ?_, fun z hz => ⟨c z, ?_⟩⟩
  · have h1 : c (e i) = Pi.single i 1 := he i
    have h2 : c (e j) = Pi.single j 1 := he j
    rw [RiemLat.ip, hc _ (e i).2 _ (e j).2, h1, h2]
    simp [Pi.single_apply, eq_comm]
  · have h : (⟨z, hz⟩ : W) = ∑ i, c z i • e i := by
      apply hinj

      rw [map_sum]
      simp only [map_smul, he]
      ext k
      simp [Pi.single_apply]
    simpa using congrArg Subtype.val h

section Cx

variable (b : Module.Basis (Fin (2 * g)) ℤ Λ)

def Pc (R : RiemLat E g Λ) : (Fin (2 * g) → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ fun k => R.P (b k)

theorem Pc_apply (R : RiemLat E g Λ) (ξ : Fin (2 * g) → ℂ) : Pc b R ξ = ∑ k, ξ k • R.P (b k) := rfl

def io (a : Λ) : Fin (2 * g) → ℂ := fun k => (b.repr a k : ℂ)

theorem star_io (a : Λ) : star (io b a) = io b a := by
  ext k
  simp [io]

theorem Pc_io (R : RiemLat E g Λ) (a : Λ) : Pc b R (io b a) = R.P a := by
  conv_rhs => rw [← b.sum_repr a]

  rw [Pc_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, io, Int.cast_smul_eq_zsmul]

def act (a : 𝓞 E) (ξ : Fin (2 * g) → ℂ) : Fin (2 * g) → ℂ := ∑ k, ξ k • io b (a • b k)

theorem Pc_act (R : RiemLat E g Λ) (a : 𝓞 E) (ξ : Fin (2 * g) → ℂ) : Pc b R (act b a ξ) = R.B a (Pc b R ξ) := by

  rw [act, map_sum, Pc_apply b R ξ, map_sum]
  simp only [map_smul, Pc_io, R.act]

theorem star_act (a : 𝓞 E) (ξ : Fin (2 * g) → ℂ) : star (act b a ξ) = act b a (star ξ) := by
  simp only [act, star_sum, star_smul, star_io, Pi.star_apply]

theorem exists_real (R : RiemLat E g Λ) (e : Fin g → ℂ) : ∃ ξ, star ξ = ξ ∧ Pc b R ξ = e := by
  have he : e ∈ Submodule.span ℝ (Set.range R.P) := by rw [SheetDecomposition.Riem.span_top]; trivial
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨_, star_io b a, Pc_io b R a⟩
  | zero => exact ⟨0, star_zero _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨ξ, h1, h2⟩ := hx
    obtain ⟨ξ', h1', h2'⟩ := hy
    exact ⟨ξ + ξ', by rw [star_add, h1, h1'], by rw [map_add (f := _), h2, h2']⟩
  | smul r x _ hx =>
    obtain ⟨ξ, h1, h2⟩ := hx
    exact ⟨(r : ℂ) • ξ, by rw [star_smul, h1]; simp, by rw [map_smul, h2]; rfl⟩

theorem exists_pair (R : RiemLat E g Λ) (e e' : Fin g → ℂ) : ∃ η, Pc b R η = e ∧ Pc b R (star η) = e' := by
  obtain ⟨ξ, h1, h2⟩ := exists_real b R ((2⁻¹ : ℂ) • (e + e'))
  obtain ⟨ξ', h1', h2'⟩ := exists_real b R ((2⁻¹ * Complex.I : ℂ) • (e' - e))
  refine ⟨ξ + Complex.I • ξ', ?_, ?_⟩
  · rw [map_add (f := _), map_smul, h2, h2', smul_smul]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination (2⁻¹ * (e' k - e k)) * Complex.I_mul_I
  · rw [star_add, star_smul, h1, h1', map_add (f := _), map_smul, h2, h2', smul_smul]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.star_def, Complex.conj_I]
    linear_combination (-2⁻¹ * (e' k - e k)) * Complex.I_mul_I

theorem ext_pair (R : RiemLat E g Λ) {η η' : Fin (2 * g) → ℂ} (h : Pc b R η = Pc b R η')
    (h' : Pc b R (star η) = Pc b R (star η')) : η = η' := by
  let Θ : (Fin (2 * g) → ℂ) →ₗ[ℂ] (Fin g → ℂ) × (Fin g → ℂ) :=
    (Pc b R).prod (Fintype.linearCombination ℂ fun k => star (R.P (b k)))
  have hΘ : ∀ ξ, Θ ξ = (Pc b R ξ, star (Pc b R (star ξ))) := fun ξ => by
    refine Prod.ext rfl ?_
    show ∑ k, ξ k • star (R.P (b k)) = star (∑ k, star ξ k • R.P (b k))
    simp only [star_sum, star_smul, Pi.star_apply, star_star]
  have hs : Function.Surjective Θ := fun ⟨e, e'⟩ => by
    obtain ⟨η, h1, h2⟩ := exists_pair b R e (star e')
    exact ⟨η, by rw [hΘ, h1, h2, star_star]⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [two_mul])).2 hs ?_
  rw [hΘ, hΘ, h, h']

theorem psi_eq (R : RiemLat E g Λ) (ξ ξ' : Fin (2 * g) → ℂ) :
    R.ip (Pc b R ξ) (Pc b R ξ') - R.ip (Pc b R (star ξ')) (Pc b R (star ξ)) =
      ∑ k, ∑ l, star (ξ k) * ξ' l * (2 * (R.form (b l) (b k) : ℂ) * Complex.I) := by
  simp only [Pc_apply, ip_sum]
  rw [Finset.sum_comm (f := fun k l => star (star ξ' k) * star ξ l * R.ip (R.P (b k)) (R.P (b l))), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h := Complex.sub_conj (R.ip (R.P (b k)) (R.P (b l)))
  have h2 : (R.ip (R.P (b k)) (R.P (b l))).im = R.form (b l) (b k) := R.im _ _
  rw [ip_conj, h2] at h
  push_cast at h
  rw [← h, Pi.star_apply, Pi.star_apply, star_star]
  ring

end Cx

theorem mem_of_eig {Ψ : Type} [Fintype Ψ] (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ)
    (W : Submodule ℂ (Fin g → ℂ)) (h : ∀ τ, eigSp B (σ τ) ≤ W) (h' : ∀ τ, eigSp B ((starRingEnd ℂ).comp (σ τ)) ≤ W) :
    W = ⊤ := by
  refine top_unique fun z _ => ?_
  obtain ⟨y, hy, rfl⟩ := SheetDecomposition.Riem.exists_decomp B z
  refine W.sum_mem fun s _ => ?_
  by_cases e : ∃ τ, σ τ = s.comp (algebraMap (𝓞 E) E)
  · obtain ⟨τ, e⟩ := e
    exact h τ (e ▸ hy s)
  · obtain ⟨τ, e'⟩ := not_not.1 (mt (hσ.2 _).2 e)
    refine h' τ ?_
    have : (starRingEnd ℂ).comp (σ τ) = s.comp (algebraMap (𝓞 E) E) := by
      rw [e']
      ext a
      simp
    exact this ▸ hy s

end RootFieldNumerics.PC
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem RootFieldNumerics.arithmetic_intersection_divisor_support : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι), IsArithVar W (e + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j W', IsArithVar W' 2 → W ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  intro hKl _ _ II hII K _ ι _ W e L hW hL hnef
  classical
  have hK : Nonempty K := hW.1
  have hDG := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system ⟨II, hII⟩)
  have hI := GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι
  have hQ := GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW
  have key := hKl ℚ K ι _ _ e (fun j => (L j).a) hI hQ (by
    intro j V hV hle
    obtain ⟨hVar, hVmap⟩ :=
      GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleGeneric.isArithVar_comap_of_isProjVarF hV
    have h0 := hnef j _ hVar (Ideal.map_le_iff_le_comap.mp hle)
    have hd := hDG K ι _ 1 (fun _ => L j) hVar (fun _ => hL j)
    rw [hVmap] at hd
    have h1 : (0 : ℝ) ≤ (GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ V (fun _ : Fin 1 => (L j).a) : ℤ) := by
      rw [← hd]; exact h0
    have h2 : (fun _ : Fin 1 => (L j).a) = ![(L j).a] := by
      funext i; fin_cases i; rfl
    rw [h2] at h1
    exact_mod_cast h1)
  have hd := hDG K ι W e L hW hL
  show 0 ≤ ptsIntegral W (pot L) (fun _ => 1)
  rw [hd]
  exact_mod_cast key
end
