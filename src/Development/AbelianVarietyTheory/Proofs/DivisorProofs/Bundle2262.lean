module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLevelFixedVectorsDefiniteUnitaryEqProd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeEqSublatticeDegreeAddLogIndex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushEquivPolPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEqOneComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2239
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.StabFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cLoc_finPt (γ : UE E n) (w : Pl E) (i j : Fin n) :
    (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)).val i j = algebraMap E (w.adicCompletion E) ((γ : GL (Fin n) E).val i j) :=
  congrArg (fun g : GL (Fin n) (Af E) => pLoc E w (g.val i j)) (GlobalTheory.BCT.FinPart.pU_finPt γ)

theorem cLoc_conj_mem_KGL {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K') (x g : finU (E := E) (n := n))
    (hg : g ∈ (globLev S K').map (MulAut.conj x).toMonoidHom) :
    ∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU (E := E) (n := n)) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro w hw
  obtain ⟨k, hk, e⟩ := Subgroup.mem_map.1 hg
  have e' : x⁻¹ * g * x = k := by
    rw [← e]
    simp [MulAut.conj_apply, mul_assoc]
  rw [e']
  have hk' : ∀ u ∈ S, ∃ a ∈ K' u, (a : GLw n u) = cLoc u k.1 := by
    simpa [globLev, Subgroup.mem_iInf] using hk
  obtain ⟨a, ha, hae⟩ := hk' w hw
  rw [← hae]
  exact Subgroup.mem_subgroupOf.1 ((hK.1 w).2.1 ha)

end GlobalTheory.BCT.StabFin


open GlobalTheory.BCT.StabFin in
theorem GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU (E := E) (n := n), Finite ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) := by
  intro E _ _ _ _ n _ S hS K' hK x
  obtain ⟨d, hd, hC⟩ := GlobalTheory.T.exists_bounded_denominator_definiteUnitary_conjugate E n S hS x
  haveI : Finite {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈
      w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1} := (GlobalTheory.T.finite_numberField_bdd_denom_conj_norm_le_one E d hd).to_subtype
  have hrat := (GlobalTheory.BCT.FinPart.finPt_props E n).2.2
  let γ : ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) → UE E n :=
    fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose
  have hγ : ∀ g, finPt (γ g) = g.1 := fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose_spec
  refine Finite.of_injective (β := Fin n → Fin n → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) *
      algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1})
    (fun g i j => ⟨((γ g : UE E n) : GL (Fin n) E).val i j, fun w => by
        have := hC g.1 (cLoc_conj_mem_KGL hK x g.1 (Subgroup.mem_inf.1 g.2).2) w i j
        rwa [← hγ g, cLoc_finPt] at this,
      fun τ => GlobalTheory.T.norm_embedding_entry_definiteUnitaryRationalPoint_le_one E n (γ g) τ i j⟩) fun g g' e => ?_
  have e1 : γ g = γ g' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact congrArg Subtype.val (congrFun (congrFun e i) j)
  apply Subtype.ext
  rw [← hγ g, ← hγ g', e1]
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.trace_heckeOperator_split_one_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) * twTr σ.ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = twTr σ.ρ (KL n w) (K' w) (f w) LinearMap.id * trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (Function.update f w ((K' w : Set (UL n w)).indicator 1))) := by
  first | exact @GlobalTheory.BCT.Peel.trOn_hop_peel | exact GlobalTheory.BCT.Peel.trOn_hop_peel | (intros; apply GlobalTheory.BCT.Peel.trOn_hop_peel <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finrank_levelFixedVectors_definiteUnitary_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ lam : InfinitePlace E → DomWeight n, (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ σ : ∀ w : Pl E, SmIrr (UL n w), (∀ w, IsCompU π w (σ w)) → (Module.finrank ℂ ↥(π ⊓ fixed (RF E n) (globLev S K')) : ℂ) = dimW lam * ∏ᶠ w ∈ S, (Module.finrank ℂ (fixed (σ w).ρ (K' w)) : ℂ) := by
  first | exact @GlobalTheory.BCT.DimFac.finrank_inf_fixed_globLev | exact GlobalTheory.BCT.DimFac.finrank_inf_fixed_globLev | (intros; apply GlobalTheory.BCT.DimFac.finrank_inf_fixed_globLev <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

theorem _root_.GlobalTheory.T.measure_translate_shell_le_div_modulus : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G) (D : Set G), μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → ∀ C : Set G, IsCompact C → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (b : G) (κ : ℝ≥0∞), (∀ m ∈ M, b * m = m * b) → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → ∀ S : Set G, MeasurableSet S → (∀ x ∈ S, ∃ u ∈ N, ∃ m ∈ M, ∃ y ∈ C, b * x = u * m * y) → κ * μ (S ∩ D) ≤ B := by
  first | exact @GlobalTheory.ResLine.modulus_mul_measure_shell_le | exact GlobalTheory.ResLine.modulus_mul_measure_shell_le | (intros; apply GlobalTheory.ResLine.modulus_mul_measure_shell_le <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open NumberField

namespace GlobalTheory.IdxMap

theorem dets_eq_detSpan (F : Type) [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) :
    GlobalTheory.IdxTensor.dets F p L = GlobalTheory.BetaEx.detSpan L := by
  unfold GlobalTheory.IdxTensor.dets GlobalTheory.BetaEx.detSpan
  congr 1
  ext d
  rw [GlobalTheory.BetaEx.mem_detSet]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Matrix.of y, hy, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

theorem idx_map_eq_colon_dets : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := by
  intro F V _ _ _ _ _ _ p φ hφ L N
  set v : Fin p → V := fun i => φ (Pi.basisFun F (Fin p) i) with hv
  have hli : LinearIndependent F v :=
    (Pi.basisFun F (Fin p)).linearIndependent.map' φ (LinearMap.ker_eq_bot.2 hφ)
  have hcoord : φ.restrictScalars (𝓞 F) = GlobalTheory.LatIndexDeg.coordMap F v := by
    refine LinearMap.ext fun x => ?_
    rw [GlobalTheory.LatIndexDeg.coordMap_apply, LinearMap.restrictScalars_apply]
    conv_lhs => rw [← (Pi.basisFun F (Fin p)).sum_repr x]

    simp [hv, map_sum, map_smul]
  have hω := GlobalTheory.LatIndexDeg.ιMulti_ne_zero_of_li v hli
  have hℓ : Function.Injective (GlobalTheory.LatIndexDeg.lineMap F (exteriorPower.ιMulti F p v)) :=
    fun s t e => smul_left_injective F hω e
  unfold GlobalTheory.FlatCM.idx
  rw [hcoord, GlobalTheory.LatIndexDeg.detSpan_map_coord, GlobalTheory.LatIndexDeg.detSpan_map_coord,
    GlobalTheory.LatIndexDeg.colon_map_of_injective _ hℓ, dets_eq_detSpan, dets_eq_detSpan]

end GlobalTheory.IdxMap
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem GlobalTheory.HorFrame.exists_ksComb_eq_single : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁), W₁ ≤ M.off → ∀ (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ (d : Fin (dimFlag Dw) → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → (∀ (K : Type) [Field K] (θ : Γ(M.X, W₁) →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s, (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd)) → ∀ (Mx : Fin (dimFlag Dw) → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (K : Type) [Field K] (ψ : Γ(M.X, W₁) →+* K) (b : HIx Dw (psiSet H)), ∃ m : Fin (dimFlag Dw) → K, ∑ a, m a • (ψ ∘ Mx a) = Pi.single b 1 := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS k W₁ hW₁ hoff hk₁ _ Q₀ hQ₀ d hd hspan Mx hMx K _ ψ b
  letI : Algebra c.F K := (ψ.comp (algebraMap c.F Γ(M.X, W₁))).toAlgebra
  let ψA : Γ(M.X, W₁) →ₐ[c.F] K := { ψ with commutes' := fun _ => rfl }
  obtain ⟨Qp, hQp⟩ := GlobalTheory.FlagMod.exists_frMap ψA Q₀
  have hk : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k := by
    rw [Category.assoc]; exact le_preimage_comp _ hk₁
  have hch : X.F.ChartFr k _ hk Qp := hQ₀.frMap hQp (Category.assoc _ _ _).symm hk
  have e : (spMap ψ ≫ tau hW₁) ≫ toFlag M = X.ptY Qp := GlobalTheory.FlagMod.FlagCover.eq_ptY hch.lies
  have ho : ⊤ ≤ (spMap ψ ≫ tau hW₁) ⁻¹ᵁ M.off := le_preimage_comp _ (tau_le hW₁ hoff)
  obtain ⟨v, hv⟩ := (hKS K Qp).exists_isTanFrame
  obtain ⟨zv, hzv, hzO⟩ := GlobalTheory.CompHS.exists_tanLift M (hv.isDef (.inl b)) e ho
  have hzW : ⊤ ≤ zv ⁻¹ᵁ W₁ := hzO W₁ (le_preimage_comp _ (tau_le hW₁ le_rfl))
  have hθ : spMap (ev zv W₁ hzW) ≫ tau hW₁ = zv := spMap_ev zv hW₁ hzW
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ zv = spMap ψ ≫ tau hW₁ := by
    have hU : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
      have := ho (Set.mem_univ s)
      rw [M.off_eq] at this
      exact this
    refine (M.existsUnique_lift _ hU).unique ?_ rfl
    rw [← cancel_mono (inc₀ X Z)]
    have h1 : zv ≫ M.σ ≫ inc₀ X Z = X.ptY (v (.inl b)) := hzv
    have h2 : ((spMap ψ ≫ tau hW₁) ≫ M.σ) ≫ inc₀ X Z = X.ptY Qp := by
      rw [← e, Category.assoc]
    rw [h2, Category.assoc, Category.assoc, h1]
    exact X.ptY_frMap (hv.isDef (.inl b))
  have hfst : ∀ s, (ev zv W₁ hzW s).fst = ψ s := by
    have h1 := ev_spMap (GlobalTheory.FlagTan.red c K).toRingHom zv W₁ hzW
      (by rw [hred]; exact le_preimage_comp _ (tau_le hW₁ le_rfl))
    have h2 := ev_spMap_tau hW₁ ψ (le_preimage_comp _ (tau_le hW₁ le_rfl))
    rw [ev_congr hred _ _ (le_preimage_comp _ (tau_le hW₁ le_rfl)), h2] at h1
    intro s
    have := congrArg (fun f : Γ(M.X, W₁) →+* K => f s) h1
    simp only [RingHom.comp_apply] at this
    rw [this]
    rfl
  obtain ⟨m, hm⟩ := hspan K (ev zv W₁ hzW)
  have hsnd : ∀ s, (ev zv W₁ hzW s).snd = ∑ a, m a * ψ (d a s).snd := fun s => by
    rw [hm s]
    exact Finset.sum_congr rfl fun a _ => by rw [← hfst]; rfl
  obtain ⟨w, hwD, hwKS, hwpt⟩ := GlobalTheory.T.exists_chart_frame_deformation_of_derivation_combination M hKS k hW₁ hk₁ Q₀ hQ₀ d hd Mx hMx K ψ hk Qp hch
    (ev zv W₁ hzW) m hfst hsnd
  have hpt : X.ptY w = X.ptY (v (.inl b)) := by
    rw [← hwpt, ← Category.assoc, hθ, hzv]
  have hx : w.x = (v (.inl b)).x := by
    have h1 := (X.lies_ptY w).1
    have h2 := (X.lies_ptY (v (.inl b))).1
    rw [hpt] at h1
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd w) (frX_snd _) (h1.symm.trans h2)]
  obtain ⟨M', -, hu⟩ := (hKS K Qp).existsUnique hwD.isTanX
  refine ⟨m, (hu _ hwKS).trans (hu _ ?_).symm⟩
  rw [hx]
  exact (hv.1 b).2

theorem GlobalTheory.HorFrame.exists_basicOpen_det_ks : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁), W₁ ≤ M.off → ∀ (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ (d : Fin (dimFlag Dw) → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → (∀ (K : Type) [Field K] (θ : Γ(M.X, W₁) →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s, (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd)) → ∀ (Mx : Fin (dimFlag Dw) → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (p : M.X), p ∈ W₁ → ∃ B : Matrix (HIx Dw (psiSet H)) (Fin (dimFlag Dw)) Γ(M.X, W₁), p ∈ M.X.basicOpen (B * Matrix.of (fun a h => Mx a h)).det := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS k W₁ hW₁ hoff hk₁ _ Q₀ hQ₀ d hd hspan Mx hMx p hp
  obtain ⟨K, hK, ψ, hbo, hden⟩ := GlobalTheory.T.exists_ringHom_field_common_denom_of_mem_isAffineOpen hW₁ p hp
  choose m hm using fun b => GlobalTheory.HorFrame.exists_ksComb_eq_single M hKS k hW₁ hoff hk₁ Q₀ hQ₀ d hd hspan Mx hMx K ψ b
  obtain ⟨a, t, ht, hat⟩ := hden (HIx Dw (psiSet H) × Fin (dimFlag Dw)) (fun bc => m bc.1 bc.2)
  refine ⟨Matrix.of fun b c => a (b, c), hbo _ ?_⟩
  have hmap : ((Matrix.of fun b c => a (b, c)) * Matrix.of (fun a h => Mx a h)).map ψ =
      Matrix.scalar (HIx Dw (psiSet H)) (ψ t) := by
    ext b h
    have e := congrFun (hm b) h
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul] at e

    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, Matrix.scalar_apply,
    Matrix.diagonal_apply]
    simp only [← hat]
    calc ∑ x, m b x * ψ t * ψ (Mx x h) = ψ t * ∑ x, m b x * ψ (Mx x h) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by
          rw [e, Pi.single_apply]
          by_cases hh : h = b
          · subst hh; simp
          · simp [hh, Ne.symm hh]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const]
  exact pow_ne_zero _ ht
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.PointMap
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GramAt

section Object

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q)

abbrev phiTP (a : Fin p) : letI := H.starRing; (pointA hv ε i X true).T →ₗ[ℤ_[ℓ]] (pointB hv ε i X).T :=
  patT (T := X.A true) hv ε i (X.lin (Sum.inl a))

abbrev phiTQ (b : Fin q) : letI := H.starRing; (pointA hv ε i X false).T →ₗ[ℤ_[ℓ]] (pointB hv ε i X).T :=
  patT (T := X.A false) hv ε i (X.lin (Sum.inr b))

variable [IsAlgClosed C] [CharZero C]


omit [NumberField K] in
theorem pairT_patT_gram {T T' : PAT H (Sp (𝓞 K))} {f f' : T.t.G ⟶ T'.t.G} (hf : Serre.IsLinearHom T.t.act T'.t.act f)
    (hf' : Serre.IsLinearHom T.t.act T'.t.act f') {g : 𝓞 E}
    (h : LamEq T'.t.PP.L f f' T.t.PP.L (T.t.act.act g) (𝟙 _)) : letI := H.starRing
    ∀ s t, pairT (patPoint hv ε i T').A ε (patT hv ε i hf s) (patT hv ε i hf' t) =
      pairT (patPoint hv ε i T).A ε ((patPoint hv ε i T).actT g s) t := by
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f' := hf'.isMonHom
  haveI := (patAct T).hom g
  intro s t
  have e := pairT_homT_of_lamEq (X := T.pol) (Y := T.pol) (A := T'.pol) (B := T.pol) hv ε (embO hv i) (patAct T) (patAct T)
    (patAct T') (patAct T) f f' ((patAct T).act g) (𝟙 _) h s t
  rw [homT_act, homT_id] at e
  exact e

theorem pairT_patT_orth (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) {A A' B : PAT H (Sp (𝓞 K))} {m m' : ℕ}
    (hA : HasType H A.t.act ρ m 0) (hA' : HasType H A'.t.act ρ 0 m') {f : A.t.G ⟶ B.t.G} {f' : A'.t.G ⟶ B.t.G}
    (hf : Serre.IsLinearHom A.t.act B.t.act f) (hf' : Serre.IsLinearHom A'.t.act B.t.act f') : letI := H.starRing
    ∀ s t, pairT (patPoint hv ε i B).A ε (patT hv ε i hf s) (patT hv ε i hf' t) = 0 := by
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := A.pol.A) (N := B.pol.A) f := hf.isMonHom
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := A'.pol.A) (N := B.pol.A) f' := hf'.isMonHom
  haveI : IsMonHom (1 : A'.pol.A ⟶ A.pol.A) := LamF.IsogSum.isMonHom_of_points _ fun T a b => by
    simp only [MonObj.comp_one, _root_.mul_one]
  intro s t
  have e := pairT_homT_of_lamEq (X := A.pol) (Y := A'.pol) (A := B.pol) (B := A.pol) hv ε (embO hv i) (patAct A)
    (patAct A') (patAct B) (patAct A) f f' (𝟙 _) 1 (lamEq_one hρ A A' B hA hA' hf hf') s t
  rw [homT_one, LinearMap.zero_apply, map_zero] at e
  exact e

theorem tateModule_gram_relations_blocks_orthogonal {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    letI := H.starRing
    (∀ a b s t, pairT (pointB hv ε i X).A ε (phiTP hv ε i X a s) (phiTP hv ε i X b t) =
      pairT (pointA hv ε i X true).A ε ((pointA hv ε i X true).actT (gP a b) s) t) ∧
    (∀ a b s t, pairT (pointB hv ε i X).A ε (phiTQ hv ε i X a s) (phiTQ hv ε i X b t) =
      pairT (pointA hv ε i X false).A ε ((pointA hv ε i X false).actT (gQ a b) s) t) ∧
    ∀ a b s t, pairT (pointB hv ε i X).A ε (phiTP hv ε i X a s) (phiTQ hv ε i X b t) = 0 :=
  ⟨fun a b => pairT_patT_gram (T := X.A true) hv ε i (X.lin (.inl a)) (X.lin (.inl b)) ((lamEq_of_isGram X h).1 a b),
    fun a b => pairT_patT_gram (T := X.A false) hv ε i (X.lin (.inr a)) (X.lin (.inr b)) ((lamEq_of_isGram X h).2 a b),
    fun a b => pairT_patT_orth (A := X.A true) (A' := X.A false) hv ε i X.ρ_sq X.typeP X.typeM (X.lin (.inl a))
      (X.lin (.inr b))⟩

end At

theorem exists_inverse_tateModule_sum_up_to_integer (X : CMObj H K ρ σ₁ p q) : letI := H.starRing
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime] (C : Type) [Field C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O]
      [Algebra O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C),
      ∃ (ψ : Fin p → ((pointB hv ε i X).T →ₗ[ℤ_[ℓ]] (pointA hv ε i X true).T))
        (ψ' : Fin q → ((pointB hv ε i X).T →ₗ[ℤ_[ℓ]] (pointA hv ε i X false).T)),
        (∀ t, ∑ k, phiTP hv ε i X k (ψ k t) + ∑ k, phiTQ hv ε i X k (ψ' k t) = N • t) ∧
        ∀ (s : Fin p → (pointA hv ε i X true).T) (s' : Fin q → (pointA hv ε i X false).T),
          (∀ l, ψ l (∑ k, phiTP hv ε i X k (s k) + ∑ k, phiTQ hv ε i X k (s' k)) = N • s l) ∧
          ∀ l, ψ' l (∑ k, phiTP hv ε i X k (s k) + ∑ k, phiTQ hv ε i X k (s' k)) = N • s' l := by
  letI := H.starRing
  haveI hP : ∀ i, IsMonHom (M := (X.A true).pol.A) (N := X.B.pol.A) (phiP X i) := fun i => (X.lin (.inl i)).isMonHom
  haveI hQ : ∀ i, IsMonHom (M := (X.A false).pol.A) (N := X.B.pol.A) (phiQ X i) := fun i => (X.lin (.inr i)).isMonHom
  obtain ⟨N, ψ, ψ', hN, hψ, hψ', h1, h2⟩ := exists_inverse X
  exact ⟨N, hN, fun ℓ _ C _ v O _ _ hv ε i => ⟨_, _, homT_inverse (B := X.B.pol) (A := (X.A true).pol)
    (A' := (X.A false).pol) hv ε (embO hv i) (patAct X.B) (patAct (X.A true)) (patAct (X.A false)) (phiP X) (phiQ X)
    ψ ψ' h1 h2⟩⟩

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q) [IsAlgClosed C] [CharZero C]

theorem sumT_injective : letI := H.starRing
    Function.Injective fun z : (Fin p → (pointA hv ε i X true).T) × (Fin q → (pointA hv ε i X false).T) =>
      ∑ k, phiTP hv ε i X k (z.1 k) + ∑ k, phiTQ hv ε i X k (z.2 k) := by
  letI := H.starRing
  obtain ⟨N, hN, h⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', -, h2⟩ := h ℓ C v O hv ε i
  have key : ∀ (P : Point ℓ v O (𝓞 E)) (x y : P.T), N • x = N • y → x = y := fun P x y e => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], ← Nat.cast_smul_eq_nsmul ℤ_[ℓ]] at e
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hN.ne') e
  exact fun z z' e => Prod.ext
    (funext fun l => key _ _ _ (((h2 z.1 z.2).1 l).symm.trans ((congrArg (ψ l) e).trans ((h2 z'.1 z'.2).1 l))))
    (funext fun l => key _ _ _ (((h2 z.1 z.2).2 l).symm.trans ((congrArg (ψ' l) e).trans ((h2 z'.1 z'.2).2 l))))

include hv ε i in
theorem gram_det_of_emb {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ (∀ a b, H.bar (gP b a) = gP a b) ∧ ∀ a b, H.bar (gQ b a) = gQ a b := by
  letI := H.starRing
  obtain ⟨N, hN, hI⟩ := exists_inverse_tateModule_sum_up_to_integer X
  obtain ⟨ψ, ψ', h1, -⟩ := hI ℓ C v O hv ε i
  obtain ⟨hP, hQ, hO⟩ := tateModule_gram_relations_blocks_orthogonal hv ε i X h
  have hg : ∀ b, 0 < (pointA hv ε i X b).A.g := fun b => (dims X).2.2.trans_eq ((dims X).1 b).symm
  have hi := sumT_injective hv ε i X
  refine ⟨det_ne_zero_of_inverse hN (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X)
      (hg true) (phiTP hv ε i X) (phiTQ hv ε i X) gP hP hO (fun t => ⟨_, _, h1 t⟩) fun s hs => ?_,
    det_ne_zero_of_inverse hN (A := pointA hv ε i X false) (A' := pointA hv ε i X true) (B := pointB hv ε i X)
      (hg false) (phiTQ hv ε i X) (phiTP hv ε i X) gQ hQ (fun a b s t => ?_)
      (fun t => ⟨_, _, (add_comm _ _).trans (h1 t)⟩) fun s hs => ?_,
    star_gram (A := pointA hv ε i X true) (B := pointB hv ε i X) (hg true) (phiTP hv ε i X) gP hP,
    star_gram (A := pointA hv ε i X false) (B := pointB hv ε i X) (hg false) (phiTQ hv ε i X) gQ hQ⟩
  · exact congrArg Prod.fst (@hi (s, 0) (0, 0) (by simp only [hs, Pi.zero_apply, map_zero, Finset.sum_const_zero]))
  · exact ((isAlt_pairT (pointB hv ε i X).A ε).neg_eq _ _).symm.trans (neg_eq_zero.2 (hO b a t s))
  · exact congrArg Prod.snd (@hi (0, s) (0, 0) (by simp only [hs, Pi.zero_apply, map_zero, Finset.sum_const_zero]))

variable [Algebra ℤ_[ℓ] C]

theorem gram_V {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    letI := H.starRing
    (∀ a b x y, (pointB hv ε i X).pairV (phiVP hv ε i X a x) (phiVP hv ε i X b y) =
      (pointA hv ε i X true).pairV ((pointA hv ε i X true).actV (gP a b) x) y) ∧
    (∀ a b x y, (pointB hv ε i X).pairV (phiVQ hv ε i X a x) (phiVQ hv ε i X b y) =
      (pointA hv ε i X false).pairV ((pointA hv ε i X false).actV (gQ a b) x) y) ∧
    ∀ a b x y, (pointB hv ε i X).pairV (phiVP hv ε i X a x) (phiVQ hv ε i X b y) = 0 := by
  letI := H.starRing
  obtain ⟨hP, hQ, hO⟩ := tateModule_gram_relations_blocks_orthogonal hv ε i X h
  refine ⟨fun a b x y => ?_, fun a b x y => ?_, fun a b x y => ?_⟩
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointA hv ε i X true) (g₂ := LinearMap.id) (hP a b) x y
    rw [LinearMap.baseChange_id] at e
    exact e
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointA hv ε i X false) (g₂ := LinearMap.id) (hQ a b) x y
    rw [LinearMap.baseChange_id] at e
    exact e
  · have e := pairV_baseChange (A := pointB hv ε i X) (B := pointB hv ε i X) (g₁ := 0) (g₂ := 0)
      (fun s t => (hO a b s t).trans (map_zero _).symm) x y
    rw [LinearMap.baseChange_zero, LinearMap.baseChange_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero] at e
    exact e

end At

theorem gram_det (X : CMObj H K ρ σ₁ p q) {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)}
    (h : IsGram X gP gQ) :
    gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ (∀ a b, H.bar (gP b a) = gP a b) ∧ ∀ a b, H.bar (gQ b a) = gQ a b := by
  obtain ⟨ε⟩ : Nonempty (Eps 2 ℂ_[2]) := inferInstance
  exact gram_det_of_emb (PadicComplexInt.integers 2) ε (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ_[2])).toRingHom X h

end Object

end GlobalTheory.GramAt
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.integral_adele_unit_congruence_sequence : ∀ (p : ℕ) [Fact p.Prime] (ε ε' : AfP p), IsIntAf ε → IsIntAf ε' → ε * ε' = 1 → ∃ u : ℕ → ℤ, (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ u (n * m) - u n) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∃ β : AfP p, IsIntAf β ∧ ε = (u n : AfP p) + (n : AfP p) * β := by
  first | (exact @GlobalTheory.UnitApprox.exists_int_approx) | (exact GlobalTheory.UnitApprox.exists_int_approx) | (intros; apply GlobalTheory.UnitApprox.exists_int_approx  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lattice_endomorphism_integral_approximation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) → ∃ h : ℕ → D.La →+ D.La, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (h n x) + n • w := by
  first | (exact @GlobalTheory.LKGeo.LiftSys.exists_lift_sys) | (exact GlobalTheory.LKGeo.LiftSys.exists_lift_sys) | (intros; apply GlobalTheory.LKGeo.LiftSys.exists_lift_sys  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.exists_dualNumber_deformation_lift_modification : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q) (zw : Sp (DualNumber K) ⟶ M.X) (hw : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ zw = z), ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ zw ≫ toFlag M = X.ptY w := by
  first | exact @GlobalTheory.CompHS.exists_isDef_lift_dualNumber | exact GlobalTheory.CompHS.exists_isDef_lift_dualNumber | (intros; apply GlobalTheory.CompHS.exists_isDef_lift_dualNumber <;> assumption)
end
