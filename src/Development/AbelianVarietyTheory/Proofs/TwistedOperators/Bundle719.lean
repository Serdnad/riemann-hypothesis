module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle712
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralVanishOfInnerVanish
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle481
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle457
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle713
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle710
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle714
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitaryPoint_prescribed_localMatrices : Big fun ch => ∀ t (j : ℕ) (hj : j ≤ _) (g : ∀ w : GlobalTheory.FunObj.locPl ch.G t, GL (Fin ((GlobalTheory.FunObj.locGrid ch.G t w.1).rank (_, j))) (GlobalTheory.FunObj.Kw w.1)), ∃ r, HasLoc t ch.S.B hj r g := by
  first | exact @GlobalTheory.RowLocBig.exists_hasLoc_big | exact GlobalTheory.RowLocBig.exists_hasLoc_big | (intros; apply GlobalTheory.RowLocBig.exists_hasLoc_big <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.vacuumBasePoint_unique_all_tuples : Big fun ch => ∀ t t' b b', IsBase t ch.S.B b → IsBase t' ch.S.B b' → b = b' := by
  first | exact @GlobalTheory.RowBaseUniq.isBase_unique | exact GlobalTheory.RowBaseUniq.isBase_unique | (intros; apply GlobalTheory.RowBaseUniq.isBase_unique <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isIteratedInvariantIntegral_vanish_of_inner_vanish : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (A B R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → (∀ i ∈ l, Split (A i) (B i) (R i) (K i)) → ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (ρ' : ∀ i, Measure ((R i).subgroupOf (B i))) (μ' : ∀ i, Measure (B i)), (∀ i ∈ l, (ρ i).IsHaarMeasure ∧ (μ i).IsHaarMeasure ∧ (ρ' i).IsHaarMeasure ∧ (μ' i).IsHaarMeasure) → ∀ (S : Finset (∀ i, H i)) (q : (∀ i, H i) → ℂ) (z : ℂ), (∀ b ∈ S, ∀ i, b i ∈ B i) → BiInv R K l q → (∀ h, (∀ i, i ∉ l → h i = 1) → q h ≠ 0 → ∃ b ∈ S, InCells A R K l b h) → NIter ρ μ q l 1 z → (∀ a : ∀ i, H i, (∀ i, a i ∈ A i) → (∀ i, i ∉ l → a i = 1) → NIter ρ' μ' (fun b : ∀ i, B i => q fun i => a i * (b i).1) l 1 0) → z = 0 := by
  first | exact @GlobalTheory.NestVan.nested_vanish | exact GlobalTheory.NestVan.nested_vanish | (intros; apply GlobalTheory.NestVan.nested_vanish <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.ArrowModel

section Moves
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z']
  [DecidableEq Z']

def moveHomeo (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) : Matrix Y Y' k ≃ₜ Matrix Z Z' k where
  toFun x := ((εT⁻¹).val * x * εS.val).submatrix σT σS
  invFun z := εT.val * z.reindex σT σS * (εS⁻¹).val
  left_inv x := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv z := by
    simp only [Matrix.reindex_apply]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one,
      Matrix.submatrix_submatrix, Equiv.symm_comp_self, Equiv.symm_comp_self, Matrix.submatrix_id_id]
  continuous_toFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_submatrix _ _
  continuous_invFun := (continuous_const.matrix_mul (continuous_id.matrix_submatrix _ _)).matrix_mul continuous_const


omit [IsNonarchimedeanLocalField k] in
theorem comp_homeo_mem_SB {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (e : X ≃ₜ X') {Φ : X' → ℂ}
    (h : Φ ∈ SB X') : Φ ∘ e ∈ SB X :=
  ⟨h.1.comp_continuous e.continuous, h.2.comp_homeomorph e⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem frame_back {K : Type} [Field K] {n N n' N' : ℕ} (h : N = n) (h' : N' = n') (L₁ : GL (Fin n) K) (L₀ : GL (Fin n') K)
    (x : Matrix (Fin N) (Fin N') K) :
    (((L₁⁻¹).val * (L₁.val.submatrix id (Fin.cast h) * x * ((L₀⁻¹).val).submatrix (Fin.cast h') id) * L₀.val).submatrix
      (Fin.cast h) (Fin.cast h')) = x := by
  subst h h'
  simp only [Fin.cast_refl, Matrix.submatrix_id_id]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

end Moves

theorem indicator_move : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' Z Z' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (εS : GL Y' k) (εT : GL Y k), εS ∈ KO k Y' → εT ∈ KO k Y → ∀ (σS : Z' ≃ Y') (σT : Z ≃ Y) (O : SB (Matrix Z Z' k)), IsOne O → ∃ Φ : SB (Matrix Y Y' k), IsOne Φ ∧ ∀ x, Φ.1 x = O.1 (((εT⁻¹).val * x * εS.val).submatrix σT σS) := by
  intro k _ _ _ _ Y Y' Z Z' _ _ _ _ _ _ _ _ εS εT hS hT σS σT O hO
  let e := moveHomeo εS εT σS σT
  refine ⟨⟨O.1 ∘ e, comp_homeo_mem_SB e O.2⟩, ?_, fun x => rfl⟩
  unfold IsOne at hO ⊢
  funext x
  change O.1 (e x) = _
  rw [hO]
  have key : (∀ r q, e x r q ∈ (ValuativeRel.valuation k).integer) ↔ ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer := by
    have h1 := GlobalTheory.SplitFlip.mul_mul_mem_matLat_iff (inv_mem hT) hS x
    rw [GlobalTheory.SplitFlip.mem_matLat_stdLat, GlobalTheory.SplitFlip.mem_matLat_stdLat] at h1
    rw [← h1]
    exact ⟨fun h r q => by simpa [e, moveHomeo] using h (σT.symm r) (σS.symm q), fun h r q => h _ _⟩
  by_cases h : ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer
  · rw [Set.indicator_of_mem (show e x ∈ {x : Matrix Z Z' k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer} from key.2 h),
      Set.indicator_of_mem (show x ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer} from h)]
  · rw [Set.indicator_of_notMem (show e x ∉ {x : Matrix Z Z' k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer} from fun H => h (key.1 H)),
      Set.indicator_of_notMem (show x ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer} from h)]

theorem exists_moved : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' Z Z' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) (Φ₁ : SB (Matrix Y Y' k)), ∃ Φ' : SB (Matrix Z Z' k), ∀ z, Φ'.1 z = Φ₁.1 (εT.val * z.reindex σT σS * (εS⁻¹).val) := by
  intro k _ _ _ _ Y Y' Z Z' _ _ _ _ _ _ _ _ εS εT σS σT Φ₁
  exact ⟨⟨Φ₁.1 ∘ (moveHomeo εS εT σS σT).symm, comp_homeo_mem_SB _ Φ₁.2⟩, fun z => rfl⟩

theorem coord_up : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (w : Pl D.host.E) (p : Place D (Kw w)), IsPlc w p → ∀ (j : ℕ) (hj : j < D.R.m) (x : Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1))) (Fin ((locGrid ch.G t w).rank (D.R.m, j))) (Kw w)), ch.S.B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, hj⟩ ⟨le_rfl, hj.le⟩ ((p.up (frRow ch.S.B t w j hj.le) (frRow ch.S.B t w (j + 1) hj) x).map fun a => cpt w (toEAf D a)) = xᵀ := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch t w p hp j hj x
  have hm : ∀ M : Matrix (Fin (ch.G.V (.grid D.R.m (j + 1))).rank) (Fin (ch.G.V (.grid D.R.m j)).rank) (Kw w),
    (M.map p.ι).map (fun a => cpt w (toEAf D a)) = M := fun M => Matrix.ext fun a b => by simp [← hp.2.1, p.π_ι]
  simp only [Place.up, GlobalTheory.FunObj.Frames.coord, frRow, frOf, hm]
  exact congrArg Matrix.transpose (frame_back _ _ _ _ x)


open Classical in
theorem model_of_vec : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) {μ0 : T}, R.toLevCh.Is μ0 → LatP ch → ∀ t, ∀ w ∈ locPl ch.G t, ∀ p, IsPlc w p → ∀ (φ : EdgeDat ch t w) j (hj : j < D.R.m) v f, IsArrVec ch t w p.e φ j hj v f → ∃ Tm₀, p.IsModel ch.W.ψ (frRow ch.S.B t w j hj.le) (frRow ch.S.B t w (j + 1) hj) Tm₀ ∧ (∀ O, IsOne O → Tm₀ O = v) ∧ ∃ Φ₀ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1))) (Fin ((locGrid ch.G t w).rank (D.R.m, j))) (Kw w)), (∀ x, Φ₀.1 x = φ (.theta D.R.m j) xᵀ) ∧ Tm₀ Φ₀ = f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch μ0 hL hLat t w hw p hp φ j hj v f hv
  obtain ⟨hθ, hSB, hTA⟩ := hv
  obtain ⟨Tm, hM, hO, Φ, hΦ, hf⟩ := GlobalTheory.T.exists_localModel_of_splitPlaceThetaFun D (Kw w) p ch.W.ψ ch.W.ψ_std _ _ _ _
    (node_isV ch.G hL (X := .grid D.R.m j) ⟨le_rfl, hj.le⟩).sd (node_isV ch.G hL (X := .grid D.R.m (j + 1)) ⟨le_rfl, hj⟩).sd
    _ _ (frRow ch.S.B t w j hj.le) (frRow ch.S.B t w (j + 1) hj) (hLat t w hw p hp j hj).1 v _ f hθ hSB hTA
  refine ⟨Tm, hM, hO, Φ, fun x => ?_, hf⟩
  rw [hΦ, if_pos (GlobalTheory.LocMod.Witness.up_half p _ _ x), coord_up ch t w p hp j hj x]

theorem weil_move : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ (Γ : GlobalTheory.SplitFlip.Grid k) (i j : ℕ), p.IsComp χS (Γ.kappa (.theta i j) (i, j + 1)) → p.IsComp χT (Γ.kappa (.theta i j) (i, j)) → ∀ (FS : Frame k S.rank (Fin (Γ.rank (i, j)))) (FT : Frame k T.rank (Fin (Γ.rank (i, j + 1)))) (Tm : SB (Matrix (Fin (Γ.rank (i, j + 1))) (Fin (Γ.rank (i, j))) k) →ₗ[ℂ] (WO S T → ℂ)), p.IsModel ψ FS FT Tm → ∀ (g : Γ.VertexGroup) (ρ : GA D S) (ρ' : GA D T), p.IsLoc FS ρ (g (i, j)) → p.IsLoc FT ρ' (g (i, j + 1)) → ∀ Φ₀ : SB (Matrix (Fin (Γ.rank (i, j + 1))) (Fin (Γ.rank (i, j))) k), ∃ Φ₁ : SB (Matrix (Fin (Γ.rank (i, j + 1))) (Fin (Γ.rank (i, j))) k), (∀ x, Φ₁.1 x = Γ.edgeFactor .one g (.theta i j) * Φ₀.1 (((g (i, j + 1))⁻¹).val * x * (g (i, j)).val)) ∧ ω (ρ, ρ') (Tm Φ₀) = Tm Φ₁ := by
  intro D k _ _ _ _ p ψ S T χS χT ω hω Γ i j hS hT FS FT Tm hM g ρ ρ' hρ hρ' Φ₀
  refine ⟨⟨_, (SB _).smul_mem (((Γ.kappa (.theta i j) (i, j + 1) * (Γ.kappa (.theta i j) (i, j))⁻¹) (Matrix.GeneralLinearGroup.det (g (i, j))) : ℂˣ) : ℂ)
    (om_mem_SB (Γ.kappa (.theta i j) (i, j + 1))⁻¹ (g (i, j)) (g (i, j + 1)) Φ₀.2)⟩, fun x => ?_,
    GlobalTheory.LocOm.omLoc D k p ψ S T χS χT ω hω _ _ hS hT _ _ FS FT Tm hM ρ (g (i, j)) ρ' (g (i, j + 1)) hρ hρ' Φ₀ _ rfl⟩
  have e1 : ∀ (a : kˣ) (r : ℕ), ((nabs k a ^ ((r : ℝ) / 2) : ℝ) : ℂ) = GlobalTheory.SplitFlip.apow a ((r : ℂ) / 2) := fun a r => by
    rw [GlobalTheory.SplitFlip.apow, Complex.ofReal_cpow (nabs_pos k a).le]; push_cast; rfl
  have e2 : ∀ (a : kˣ) (r : ℕ), ((nabs k a ^ (-((r : ℝ) / 2)) : ℝ) : ℂ) = GlobalTheory.SplitFlip.apow a (-((r : ℂ) / 2)) := fun a r => by
    rw [GlobalTheory.SplitFlip.apow, Complex.ofReal_cpow (nabs_pos k a).le]; push_cast; rfl
  simp only [om, GlobalTheory.SplitFlip.Grid.edgeFactor, Pi.smul_apply, smul_eq_mul, Fintype.card_fin, e1, e2, GlobalTheory.SplitFlip.Assignment.read,
    GlobalTheory.SplitFlip.gdet_invT, GlobalTheory.SplitFlip.apow_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    neg_div, neg_neg]
  have hA := Units.ne_zero ((Γ.kappa (.theta i j) (i, j + 1)) (Matrix.GeneralLinearGroup.det (g (i, j))))
  generalize ((Γ.kappa (.theta i j) (i, j + 1)) (Matrix.GeneralLinearGroup.det (g (i, j))) : ℂ) = A at hA ⊢
  simp only [GlobalTheory.SplitFlip.Edge.src, GlobalTheory.SplitFlip.Edge.tgt, inv_inv]
  field_simp

theorem arrow_model : Big fun ch => LatP ch → ChrP ch → ArrP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  intro hLat hChr t w hw p hp φ j hj v f hv ε g hε a ρ a' ρ' hρ hρ' Z Z' _ _ _ _ σ σ'
  obtain ⟨Tm₀, hM, hO, Φ₀, hΦ₀, hf⟩ := model_of_vec ch hL hLat t w hw p hp φ j hj v f hv
  have hC := (hChr t w hw p hp).2.2 j hj
  have hωis := ch.W.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩
  obtain ⟨Φ₁, hΦ₁, hω⟩ := weil_move D (Kw w) p ch.W.ψ _ _ _ _ (ch.W.om (.mu t D.R.m j)) hωis (locGrid ch.G t w) D.R.m j hC.1 hC.2
    _ _ Tm₀ hM (ε * g) ρ ρ' hρ hρ' Φ₀
  obtain ⟨Tm', hM', hT'⟩ := GlobalTheory.T.exists_localModel_movedFrames D (Kw w) p ch.W.ψ _ _ _ _ (ch.W.om (.mu t D.R.m j)) hωis _ _ Z' Z _ _ Tm₀ hM a a'
    (ε (D.R.m, j)) (ε (D.R.m, j + 1)) σ σ'
  refine ⟨Tm', hM', fun O hO' => ?_, ?_⟩
  · obtain ⟨Φ, hΦ, hΦO⟩ := indicator_move (Kw w) _ _ _ _ (ε (D.R.m, j)) (ε (D.R.m, j + 1)) (hε _) (hε _) σ σ' O hO'
    rw [hT' Φ O hΦO, hO Φ hΦ]
  · obtain ⟨Φ', hΦ'⟩ := exists_moved (Kw w) _ _ _ _ (ε (D.R.m, j)) (ε (D.R.m, j + 1)) σ σ' Φ₁
    refine ⟨Φ', fun z => ?_, ?_⟩
    · rw [hΦ', hΦ₁, hΦ₀, phiM]
      congr 2
      simp only [Pi.mul_apply, Units.val_mul, _root_.mul_inv_rev, Matrix.transpose_mul, Matrix.mul_assoc]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]
    · rw [hT' Φ₁ Φ' ?_, ← hω, ← hf, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
      intro x
      rw [hΦ']
      congr 1
      rw [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Equiv.self_comp_symm, Matrix.submatrix_id_id,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.ArrowModel

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LastStepOne

theorem first_step_flat : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hLoc : LocP ch) (hBes : BesP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (r r₀ h : Pts ch.G)
    (hpts : IsPts ch t w β p.e r r₀ h) (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt ch.G j 0 hj))
    (h₁ : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1))
    (h₂ : topRank (locGrid ch.G t w) j + (0 + 1) = (locGrid ch.G t w).rank (D.R.m, j)),
    ∃ (F₀ : Frame (Kw w) (besAt ch.G hM j 0 hj vN).V₀.rank (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit))
      (T₁ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)) →ₗ[ℂ]
        (WO (besAt ch.G hM j 0 hj vN).V₀ (ch.G.V (.top (j + 1))) → ℂ)),
      p.IsCoreFrame (besAt ch.G hM j 0 hj vN) (p.xi ^ 0)⁻¹ (frTop ch.S.toGridChoice t w j (by omega)) F₀ ∧
      p.IsModel ch.W.ψ F₀ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) T₁ ∧
      (∀ O, IsOne O → T₁ O = GlobalTheory.Unf.flatBF (lastAt ch.G ch.W t hM j hj vN).s
        ((lastAt ch.G ch.W t hM j hj vN).s.om ((h * r₀) j, 1) (v ⟨j, by omega⟩))) ∧
      ∃ Φ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)),
        Φ.1 = GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) (0 + 1) (datC h₁ h₂
          (phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ (.theta D.R.m j))) ∧
        T₁ Φ = GlobalTheory.Unf.flatBF (lastAt ch.G ch.W t hM j hj vN).s
          ((lastAt ch.G ch.W t hM j hj vN).s.om ((h * r) j, 1) (f ⟨j, by omega⟩)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hChr hArr hLoc hBes hJac t w hw p hp β r r₀ h hpts M hM φ v f hvf j hj vN h₁ h₂
  have hm := D.R.two_le_m
  have hjm : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  have hev : Even j := by
    obtain ⟨a, ha⟩ := D.R.m_even
    exact ⟨a - 1, by omega⟩
  have hL := hLoc t w hw p hp β r r₀ h hpts j hjm.le
  have hc := hChr t w hw p hp

  have hone : p.IsLoc (frRow ch.S.B t w (j + 1) hjm) 1
      ((epsV ch.G t w * (repsAt ch.G t w).elt β) (D.R.m, j + 1)) := by
    have e1 : (epsV ch.G t w * (repsAt ch.G t w).elt β) (D.R.m, j + 1) = 1 := by
      rw [Pi.mul_apply, epsV_eq_one t w (by omega), elt_eq_one t w β (by omega), one_mul]
    have hmt : Formalism.L2.Theta.mt (ch.G.V (.grid D.R.m (j + 1))) 1 = 1 := by simp [Formalism.L2.Theta.mt]
    refine ⟨fun a b => ?_, ?_⟩
    · rw [hmt, sub_self]
      simp
    · rw [e1, hmt, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one, Matrix.mul_one, (frRow ch.S.B t w (j + 1) hjm).βγ]
  obtain ⟨Tm, hTm, hTmO, Φ, hΦ, hTmΦ⟩ := hArr t w hw p hp φ j hjm (v ⟨j, hjm⟩) (f ⟨j, hjm⟩) (hvf ⟨j, hjm⟩)
    (epsV ch.G t w) ((repsAt ch.G t w).elt β) (epsV_mem t w) (h j * r₀ j) ((r₀ j)⁻¹ * r j) 1 1 hL.1 hone
    _ _ (frame h₂) (frame h₁)
  have hB := hBes t w hw p hp M hM j 0 hj vN (h j * r₀ j) (hL.2.1 hev) (0 + 1) h₂
  have hJ := hJac t w hw p hp M hM j 0 hj vN 1 (Or.inl ⟨rfl, rfl⟩) 0 h₁
  have hs : ((p.xi ^ 0)⁻¹ : Kw w) ≠ 0 := by simp
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.LocMod.Witness.exists_core p (besAt ch.G hM j 0 hj vN) hs
    (frTop ch.S.toGridChoice t w j (by omega))
  have hBF := GlobalTheory.FlatBFLoc.flatBF_of_laws D (GlobalTheory.Unf.Flat.flatLaw D) (GlobalTheory.FinPl.flatLaws_all D) (GlobalTheory.LocOm.omLoc D)
  obtain ⟨T₀, hT₀, hT₀e⟩ := hBF (Kw w) p (unitVol w) (isUnitVol_unitVol w).1 ch.W.ψ (psiAt ch.W w) hc.1 0
    (besAt ch.G hM j 0 hj vN) (lastAt ch.G ch.W t hM j hj vN).J (lastAt ch.G ch.W t hM j hj vN).s (p.xi ^ 0)⁻¹ hs
    _ _ 0 (frTop ch.S.toGridChoice t w j (by omega)) F₀ _ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) _ hF₀ hB hJ Tm hTm
  have hψc : Continuous (psiAt ch.W w) := hc.2.1.continuous
  have hfl := GlobalTheory.LocFlat.flat_SB_onto (Kw w) (psiAt ch.W w) (unitVol w) hψc (isUnitVol_unitVol w).1
    (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j)) 0 (0 + 1) le_rfl
  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator (Kw w) (psiAt ch.W w) (unitVol w) hc.2.1 (isUnitVol_unitVol w)
    (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j)) (Fin (topRank (locGrid ch.G t w) j)) 0 (0 + 1)
  refine ⟨F₀, T₀, hF₀, hT₀, fun O hO => ?_, ⟨_, (hfl.1 le_rfl).1 Φ.1 Φ.2⟩, ?_, ?_⟩
  · let Ob : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (0 + 1)) (Kw w)) :=
      ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
    have hOb : GlobalTheory.LocMod.IsOne Ob := rfl
    have e : O.1 = GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) (0 + 1) Ob.1 := by
      rw [hO]
      show _ = GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) (0 + 1) (Set.indicator _ _)
      rw [hun.1, ite_eq_right (by omega)]
    refine (hT₀e Ob O e).symm.trans ?_
    exact congrArg _ (hTmO Ob hOb)
  · show GlobalTheory.LocFlat.flCol _ _ _ Φ.1 = _
    congr 1
    funext z
    exact hΦ z
  · refine (hT₀e Φ ⟨_, (hfl.1 le_rfl).1 Φ.1 Φ.2⟩ rfl).symm.trans ?_
    refine congrArg _ (hTmΦ.trans ?_)
    have e : (h j * r₀ j * ((r₀ j)⁻¹ * r j), (1 : GA D (ch.G.V (.grid D.R.m (j + 1)))) * 1) = (h j * r j, 1) := by
      rw [mul_one, mul_assoc, mul_inv_cancel_left]
    rw [e]
    rfl

end GlobalTheory.LastStepOne
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowAssemble
open GlobalTheory.RowRep GlobalTheory.RowBaseUniq
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem piAt_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    infPart D e = 0 ∧ (∀ w ∈ P, piAt w e = 1) ∧ ∀ w ∉ P, piAt w e = 0 :=
  GlobalTheory.FunObj.Comparison₂.cpt_idemSum he

theorem isIdemSum_one {ew : AE D} {w : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt ew w) : IsIdemSum ew {w} :=
  ⟨⟨fun _ => ew, fun _ hx => by rw [Finset.mem_singleton.1 hx]; exact h, by simp⟩, h.1.2.1⟩

theorem suppAt_one {e : AE D} {V : HSp D} : SuppAt e V 1 := fun i j => by
  change (e + cA D e) * (mt V 1 - 1) i j = (mt V 1 - 1) i j
  rw [show mt V (1 : GA D V) = 1 from rfl, sub_self]
  simp

theorem suppAt_mul {e : AE D} {V : HSp D} {g h : GA D V} (hg : SuppAt e V g) (hh : SuppAt e V h) :
    SuppAt e V (g * h) := by
  intro i j
  have e1 : mt V (g * h) - 1 = (mt V g - 1) * (mt V h - 1) + (mt V g - 1) + (mt V h - 1) := by
    rw [show mt V (g * h) = mt V g * mt V h from rfl]
    noncomm_ring
  have s : (e + cA D e) * ((mt V g - 1) * (mt V h - 1)) i j = ((mt V g - 1) * (mt V h - 1)) i j := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hg i k]
  rw [e1, Matrix.add_apply, Matrix.add_apply, mul_add, mul_add, s, hg i j, hh i j]

theorem suppAt_of_le {e e' : AE D} {V : HSp D} {g : GA D V}
    (hf : (e' + cA D e') * (e + cA D e) = e' + cA D e') (h : SuppAt e' V g) : SuppAt e V g := fun i j => by
  linear_combination (1 - (e + cA D e)) * h i j + (mt V g - 1) i j * hf

theorem loc_eq_one {V : HSp D} {a : AE D} {g : GA D V} (h : SuppAt a V g) {u : Pl D.host.E}
    (hu : piAt u (a + cA D a) = 0) : GlobalTheory.StdFrames.loc u (Lev.finE V g) = 1 := by
  refine Units.ext ?_
  change (mt V g).map (piAt u) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Kw u))
  rw [← Matrix.map_one (piAt u) (map_zero _) (map_one _)]
  refine Matrix.ext fun i j => ?_
  have k := congrArg (piAt u) (h i j)
  rw [RingHom.map_mul, hu, zero_mul, Matrix.sub_apply, RingHom.map_sub] at k
  exact sub_eq_zero.1 k.symm

theorem exists_subgroup_elem_localComponents_subset {V : HSp D} {P : Finset (Pl D.host.E)} {e : AE D} (H : Subgroup (GA D V)) (r : GA D V)
    (hw : ∀ w ∈ P, ∃ h ∈ H, SuppAt e V h ∧ GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r) ∧
      ∀ u ∈ P, u ≠ w → GlobalTheory.StdFrames.loc u (Lev.finE V h) = 1) :
    ∀ Q ⊆ P, ∃ y ∈ H, SuppAt e V y ∧ (∀ u ∈ Q, GlobalTheory.StdFrames.loc u (Lev.finE V y) = GlobalTheory.StdFrames.loc u (Lev.finE V r)) ∧
      ∀ u ∈ P, u ∉ Q → GlobalTheory.StdFrames.loc u (Lev.finE V y) = 1 := by
  classical
  intro Q
  refine Finset.induction_on Q ?_ ?_
  · intro _
    exact ⟨1, H.one_mem, suppAt_one, by simp, fun u _ _ => by rw [map_one, map_one]⟩
  · intro w Q hwQ ih hQ
    obtain ⟨y, hy, sy, ly, oy⟩ := ih ((Finset.subset_insert _ _).trans hQ)
    obtain ⟨h, hh, sh, lh, oh⟩ := hw w (hQ (Finset.mem_insert_self _ _))
    refine ⟨y * h, H.mul_mem hy hh, suppAt_mul sy sh, fun u hu => ?_, fun u hu hn => ?_⟩
    · rw [map_mul, map_mul]
      rcases Finset.mem_insert.1 hu with hu | hu
      · rw [hu, oy w (hQ (Finset.mem_insert_self _ _)) hwQ, lh, one_mul]
      · rw [ly u hu, oh u (hQ (Finset.mem_insert_of_mem hu)) (fun h' => hwQ (h' ▸ hu)), mul_one]
    · rw [map_mul, map_mul, oy u hu (fun h' => hn (Finset.mem_insert_of_mem h')),
        oh u hu (fun h' => hn (h' ▸ Finset.mem_insert_self _ _)), one_mul]

theorem mem_of_loc : ∀ {D : D7} (V : HSp D) (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ (H : Subgroup (GA D V)) (r : GA D V), SuppAt e V r →
    (∀ w ∈ P, ∀ ew : AE D, Formalism.L2.NTheta.IsIdemAt ew w → ∃ h ∈ H, SuppAt ew V h ∧
      GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r)) → r ∈ H := by
  intro D V P e he H r hr hyp
  classical
  obtain ⟨e0, e1, e2⟩ := piAt_idemSum he
  obtain ⟨⟨es, hes, -⟩, hec⟩ := he
  have hce : ∀ u ∈ P, piAt u (cA D e) = 0 := fun u hu => by
    have k := congrArg (piAt u) hec
    rwa [RingHom.map_mul, e1 u hu, one_mul, map_zero] at k
  have key : ∀ w ∈ P, ∃ h ∈ H, SuppAt e V h ∧ GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r) ∧
      ∀ u ∈ P, u ≠ w → GlobalTheory.StdFrames.loc u (Lev.finE V h) = 1 := by
    intro w hw
    obtain ⟨f0, f1, f2⟩ := piAt_idemSum (isIdemSum_one (hes w hw))
    have a : es w * e = es w := ae_ext (by rw [RingHom.map_mul, f0, zero_mul]) fun Q => by
      change piAt Q (es w * e) = piAt Q (es w)
      rw [RingHom.map_mul]
      by_cases hQ : Q = w
      · rw [hQ, f1 w (Finset.mem_singleton_self _), e1 w hw, one_mul]
      · rw [f2 Q (by simpa using hQ), zero_mul]
    have b : es w * cA D e = 0 := by rw [← a, mul_assoc, hec, mul_zero]
    have c : cA D (es w) * e = 0 := by
      have k := congrArg (cA D) b
      rwa [RingHom.map_mul, Formalism.L2.Theta.cA_cA, map_zero] at k
    have d : cA D (es w) * cA D e = cA D (es w) := by rw [← RingHom.map_mul, a]
    have hf : (es w + cA D (es w)) * (e + cA D e) = es w + cA D (es w) := by linear_combination a + b + c + d
    obtain ⟨h, hH, sh, lh⟩ := hyp w hw (es w) (hes w hw)
    refine ⟨h, hH, suppAt_of_le hf sh, lh, fun u hu hne => loc_eq_one sh ?_⟩
    have k := congrArg (piAt u) d
    rw [RingHom.map_mul, hce u hu, mul_zero] at k
    rw [RingHom.map_add (f := _), f2 u (by simpa using hne), ← k, add_zero]
  obtain ⟨y, hy, sy, ly, -⟩ := exists_subgroup_elem_localComponents_subset H r key P subset_rfl
  have k : e • mt V r = e • mt V y := smul_eq_of_loc e0 fun w => by
    by_cases hw : w ∈ P
    · exact .inr (ly w hw).symm
    · exact .inl (e2 w hw)
  have hry : r = y := Subtype.ext (Units.ext (eq_of_halves hr sy k (smul_conj k)))
  rw [hry]
  exact hy

end GlobalTheory.RowAssemble

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_prod_single_place_pieces_of_suppAt : ∀ {D : D7} (V : HSp D) (P : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D), (∀ w ∈ P, Formalism.L2.NTheta.IsIdemAt (es w) w) → (∑ w ∈ P, es w) * cA D (∑ w ∈ P, es w) = 0 → ∀ r : GA D V, SuppAt (∑ w ∈ P, es w) V r → ∃ h : P → GA D V, (∀ w, SuppAt (es w.1) V (h w)) ∧ (∀ w, (mt V (h w)).map (GlobalTheory.RowRep.piAt w.1) = (mt V r).map (GlobalTheory.RowRep.piAt w.1)) ∧ r = (Finset.univ.toList.map h).prod := by
  first | exact @GlobalTheory.PlaceCut.exists_prod_pieces | exact GlobalTheory.PlaceCut.exists_prod_pieces | (intros; apply GlobalTheory.PlaceCut.exists_prod_pieces <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.rowTest_mem_fourierJacobiGroup_of_sumFrame_symmetric : ∀ {D : D7} {A B : HSp D} {c σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ), 1 ≤ σ → ∀ (w : Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D)) (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w), IsSumFrame d w β β' u → (∀ p, u p ≠ 0) → ∀ {a b : ℕ} (_ : a = A.rank) (hb : b = B.rank) (hab : a + c = b) (q : GlobalTheory.FinPl.SplitPt D (Kw w)), (∀ x, q.pr x = GlobalTheory.RowRep.piAt w x) → ∀ g : GA D B, SuppAt q.e B g → frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c → g ∈ jacGrp (jacDec d h) := by
  exact @GlobalTheory.RowRepLoc.mem_jacGrp_of_symR
end
end
