module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.quadraticHeckeCharCM_eq_ideleInfiniteSign_finiteTrivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    (∀ v, (b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1) →
    (GlobalTheory.GalOfCusp.quadChar E).1 b = GlobalTheory.ConsEta.infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) := by
  first | exact @GlobalTheory.EtaInfSign.quadChar_eq_infSign | exact GlobalTheory.EtaInfSign.quadChar_eq_infSign | (intros; apply GlobalTheory.EtaInfSign.quadChar_eq_infSign <;> assumption)
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} {β : G.Cˣ} {x : (AfP p ⊗[ℚ] G.C)ˣ}
  {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t} {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)}

theorem posV_val_ne_zero (z : PosV G v β) : z.1 ≠ 0 := by
  intro h
  have hz := z.2
  rw [h] at hz
  simp at hz

theorem fixL_smul_vec_iff (y : grp G β) (z : Fin G.n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    FixL G v β y (c • z) ↔ FixL G v β y z := by
  unfold FixL
  simp only [Matrix.mulVec_smul]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [smul_comm e c z] at he
    exact smul_right_injective _ hc he
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [he, smul_comm]⟩

variable (G v β x t hx Kf K')

def orbOfDat (d : Dat G v β) : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
  Quotient.mk'' (LeftCosets.mk _ _ d.1, (Projectivization.mk ℂ d.2.1 (posV_val_ne_zero d.2) : PLv G v β))

theorem orbOfDat_eq_of_same {a b : Dat G v β} (h : Same G v β x t hx Kf K' a b) :
    orbOfDat G v β x t hx Kf K' a = orbOfDat G v β x t hx Kf K' b := by
  obtain ⟨g, k, c, hk1, hk2, hc, h1, h2⟩ := h
  symm
  apply Quotient.sound
  refine ⟨g, Prod.ext ?_ ?_⟩
  · change g • LeftCosets.mk ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1 = LeftCosets.mk _ _ b.1
    rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk, h1, MonoidHom.prod_apply, inv_mul_cancel_left]
    exact Subgroup.mem_prod.2 ⟨hk1, hk2⟩
  · change Projectivization.map (Matrix.toLin' (toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ))
      (toV_injective G v β g) (Projectivization.mk ℂ a.2.1 (posV_val_ne_zero a.2)) =
      Projectivization.mk ℂ b.2.1 (posV_val_ne_zero b.2)
    rw [Projectivization.map_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨c⁻¹, ?_⟩
    rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul, Matrix.toLin'_apply]

def DatWt (f : G.GAf → ℂ) (f' : Gr G 1 → ℂ) (d : Dat G v β) : Prop :=
  ∃ y : grp G β, FixL G v β y d.2.1 ∧
    f (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * f' (d.1.2⁻¹ * toP1 G β y * d.1.2) ≠ 0

theorem datWt_iff_of_same {f : G.GAf → ℂ} {f' : Gr G 1 → ℂ} (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g)
    (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) {a b : Dat G v β} (h : Same G v β x t hx Kf K' a b) :
    DatWt G v β x t hx f f' a ↔ DatWt G v β x t hx f f' b := by
  obtain ⟨g, k, c, hk1, hk2, hc, h1, h2⟩ := h
  have e1 : ∀ y : grp G β, b.1.1⁻¹ * toAfF G β x t hx (g * y * g⁻¹) * b.1.1 =
      k.1⁻¹ * (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * k.1 := by
    intro y; rw [h1]; simp only [Prod.fst_mul, map_mul, map_inv]; group
  have e2 : ∀ y : grp G β, b.1.2⁻¹ * toP1 G β (g * y * g⁻¹) * b.1.2 =
      k.2⁻¹ * (a.1.2⁻¹ * toP1 G β y * a.1.2) * k.2 := by
    intro y; rw [h1]; simp only [Prod.snd_mul, map_mul, map_inv]; group
  have efix : ∀ y : grp G β, FixL G v β (g * y * g⁻¹) b.2.1 ↔ FixL G v β y a.2.1 := by
    intro y
    rw [h2, fixL_smul_vec_iff _ _ hc]
    exact (fixL_conj_iff p G v β y g a.2.1).symm
  constructor
  · rintro ⟨y, hy, hne⟩
    refine ⟨g * y * g⁻¹, (efix y).2 hy, ?_⟩
    rwa [e1, e2, hf _ hk1, hf' _ hk2]
  · rintro ⟨y', hy', hne⟩
    obtain ⟨y, rfl⟩ : ∃ y, y' = g * y * g⁻¹ := ⟨g⁻¹ * y' * g, by group⟩
    refine ⟨y, (efix y).1 hy', ?_⟩
    rwa [e1, e2, hf _ hk1, hf' _ hk2] at hne

end GlobalTheory.CxUnfold
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfold

theorem minpoly_units_conj {F A : Type*} [Field F] [Ring A] [Algebra F A] (u : Aˣ) (x : A) :
    minpoly F ((u : A) * x * ((u⁻¹ : Aˣ) : A)) = minpoly F x := by
  let e : A ≃ₐ[F] A :=
    { toFun := fun z => (u : A) * z * ((u⁻¹ : Aˣ) : A)
      invFun := fun z => ((u⁻¹ : Aˣ) : A) * z * u
      left_inv := fun z => by simp [mul_assoc]
      right_inv := fun z => by simp [mul_assoc]
      map_mul' := fun z w => by simp [mul_assoc]
      map_add' := fun z w => by simp [mul_add, add_mul]
      commutes' := fun r => by
        show (u : A) * algebraMap F A r * ((u⁻¹ : Aˣ) : A) = algebraMap F A r
        rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one] }
  exact minpoly.algEquiv_eq e x

theorem fixL_smul_iff {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β)
    (z : Fin G.n → ℂ) (c : ℂ) (hc : c ≠ 0) : FixL G v β y (c • z) ↔ FixL G v β y z := by
  unfold FixL
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    rw [Matrix.mulVec_smul, smul_comm d c z] at hd
    exact smul_right_injective _ hc hd
  · rintro ⟨d, hd⟩
    exact ⟨d, by rw [Matrix.mulVec_smul, hd, smul_comm]⟩

end GlobalTheory.CxUnfold

namespace GlobalTheory.CxUnfold

theorem rep_smul {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (η : grp G β)
    (l : PLv G v β) : ∃ c : ℂ, c ≠ 0 ∧
      Projectivization.rep ((η • l : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)) =
        c • ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
          Projectivization.rep (l : Projectivization ℂ (Fin G.n → ℂ))) := by
  set w := Projectivization.rep (l : Projectivization ℂ (Fin G.n → ℂ))
  have hw : w ≠ 0 := Projectivization.rep_nonzero _
  have hMw : (toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w ≠ 0 := by
    intro h0
    apply hw
    apply toV_injective G v β η
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h0, Matrix.mulVec_zero]
  have hl : ((η • l : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)) =
      Projectivization.mk ℂ ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) hMw := by
    show Projectivization.map _ _ (l : Projectivization ℂ (Fin G.n → ℂ)) = _
    conv_lhs => rw [← Projectivization.mk_rep (l : Projectivization ℂ (Fin G.n → ℂ))]
    rw [Projectivization.map_mk]
    simp only [Matrix.toLin'_apply]
    rfl
  rw [hl]
  have h2 := Projectivization.mk_rep (Projectivization.mk ℂ ((toV G v β η : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) hMw)
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ (Projectivization.rep_nonzero _) hMw).1 h2
  exact ⟨c, c.ne_zero, by rw [← hc, Units.smul_def]⟩

end GlobalTheory.CxUnfold

namespace GlobalTheory.CxUnfold

end GlobalTheory.CxUnfold
end
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

variable {p : ℕ} [Fact p.Prime]

def IntC (G : HTGroup p) (w : AwayP p) (a : w.1.adicCompletion ℚ ⊗[ℚ] G.C) : Prop :=
  ∀ i, coordL G w a i ∈ w.1.adicCompletionIntegers ℚ

end GlobalTheory.FinClsLoc
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AwayOrb.Cpt
open scoped RestrictedProduct
variable {p : ℕ} [Fact p.Prime]

theorem eventually_int_of_isCompact (K : Set (AfP p)) (hK : IsCompact K) :
    ∀ᶠ w in Filter.cofinite, ∀ x ∈ K, AfP.eval w x ∈ w.1.adicCompletionIntegers ℚ := by
  let U : Finset (AwayP p) → Set (AfP p) := fun F =>
    {f : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ] |
      ∀ i, i ∉ F → f.1 i ∈ (i.1.adicCompletionIntegers ℚ : Set (i.1.adicCompletion ℚ))}
  have hU : ∀ F, IsOpen (U F) := fun F =>
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun i => i ∉ F)
  have hcov : K ⊆ ⋃ F, U F := by
    intro x _
    have hx := x.2
    rw [Filter.eventually_cofinite] at hx
    refine Set.mem_iUnion.2 ⟨hx.toFinset, fun i hi => ?_⟩
    by_contra h
    exact hi (hx.mem_toFinset.2 h)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcov
  let S : Finset (AwayP p) := t.biUnion id
  rw [Filter.eventually_cofinite]
  refine S.finite_toSet.subset fun w hw => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hw
  obtain ⟨x, hxK, hxw⟩ := hw
  obtain ⟨F, hF, hxF⟩ := Set.mem_iUnion₂.1 (ht hxK)
  by_contra hwS
  exact hxw (hxF w fun hwF => hwS (Finset.mem_biUnion.2 ⟨F, hF, hwF⟩))

theorem repr_map_eval (G : HTGroup p) (w : AwayP p) (x : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) (Module.finBasis ℚ G.C)).repr
        (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) x) i =
      AfP.eval w ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul r c =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]

theorem continuous_coord (G : HTGroup p) (i : Fin (Module.finrank ℚ G.C)) :
    Continuous fun x : G.GAf => (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
      (((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap
    ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).coord i)).comp
    (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val))

theorem continuous_coord_inv (G : HTGroup p) (i : Fin (Module.finrank ℚ G.C)) :
    Continuous fun x : G.GAf => (Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
      ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) i := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  exact (IsModuleTopology.continuous_of_linearMap
    ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).coord i)).comp
    (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val))

theorem continuous_sim (G : HTGroup p) :
    Continuous fun x : G.GAf => (((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)

theorem continuous_sim_inv (G : HTGroup p) :
    Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  exact Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)

theorem eventually_mem_intPts (G : HTGroup p) (Ω : Set G.GAf) (hΩ : IsCompact Ω) :
    ∀ᶠ w in Filter.cofinite, ∀ h ∈ Ω, compL G w h ∈ intPts G w := by
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i, ∀ h ∈ Ω, AfP.eval w
      ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
        (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i) ∈ w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i =>
      (eventually_int_of_isCompact _ (hΩ.image (continuous_coord G i))).mono fun w hw h hh =>
        hw _ (Set.mem_image_of_mem _ hh)
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i, ∀ h ∈ Ω, AfP.eval w
      ((Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)).repr
        ((((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) i) ∈
        w.1.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun i =>
      (eventually_int_of_isCompact _ (hΩ.image (continuous_coord_inv G i))).mono fun w hw h hh =>
        hw _ (Set.mem_image_of_mem _ hh)
  have h3 := eventually_int_of_isCompact _ (hΩ.image (continuous_sim G))
  have h4 := eventually_int_of_isCompact _ (hΩ.image (continuous_sim_inv G))
  filter_upwards [h1, h2, h3, h4] with w hw1 hw2 hw3 hw4 h hh
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · have e := repr_map_eval G w (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C)) i
    have := hw1 i h hh
    rw [← e] at this
    exact this
  · have e := repr_map_eval G w ((((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C) i
    have := hw2 i h hh
    rw [← e] at this
    exact this
  · exact hw3 _ (Set.mem_image_of_mem _ hh)
  · exact hw4 _ (Set.mem_image_of_mem _ hh)

end GlobalTheory.AwayOrb.Cpt

theorem GlobalTheory.AwayOrb.eventually_compL_mem_intPts : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf),
    IsCompact Ω → ∀ᶠ w in Filter.cofinite, ∀ h ∈ Ω, compL G w h ∈ intPts G w :=
  fun _ _ G Ω hΩ => GlobalTheory.AwayOrb.Cpt.eventually_mem_intPts G Ω hΩ

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitVacF

end GlobalTheory.SplitVacF

end

noncomputable section

namespace GlobalTheory.SplitVacF

open GlobalTheory.SplitInvFormF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}

theorem isSplitIdemF_conj {e : AEF F E} (he : IsSplitIdemF σ e) : IsSplitIdemF σ (cAF σ e) := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hpl, ?_⟩
  · rw [cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, mul_comm, h2]
  · rw [cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, add_comm, hsum]

theorem mem_conjHalf_conj {e : AEF F E} (he : IsSplitIdemF σ e) {x : WOF F E nS nT} (hx : ∀ i j, e * x i j = x i j) :
    x ∈ conjHalf σ (cAF σ e) nS nT := fun i j => by rw [cAF_cAF he]; exact hx i j

theorem fin_of_mem {e : AEF F E} (he : IsSplitIdemF σ e) {u : WOF F E nS nT} (hu : u ∈ conjHalf σ e nS nT) :
    u.map (infPartF F E) = 0 := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  have hs := congrArg (infPartF F E) hsum
  rw [map_add (f := _), GlobalTheory.WeilPartsF.infPartF_placeIdem hpl] at hs
  have hc : infPartF F E (cAF σ e) = 0 := by
    have a1 : infPartF F E (cAF σ e) * infPartF F E (cAF σ e) = infPartF F E (cAF σ e) := by
      rw [← map_mul, ← map_mul, h1]
    have a2 : infPartF F E (cAF σ e) * infPartF F E e = 0 := by rw [← map_mul, mul_comm, h2, map_zero]
    linear_combination -a1 - a2 + infPartF F E (cAF σ e) * hs
  ext i j
  show infPartF F E (u i j) = 0
  rw [← hu i j, map_mul, hc, zero_mul]

theorem commF_add_left (u u' y : WOF F E nS nT) :
    commF σ JS JT xi0 ψ (u + u') y = commF σ JS JT xi0 ψ u y * commF σ JS JT xi0 ψ u' y := by
  unfold commF
  rw [← AddChar.map_add_eq_mul, GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right]
  congr 1; ring

theorem commF_add_right (u y y' : WOF F E nS nT) :
    commF σ JS JT xi0 ψ u (y + y') = commF σ JS JT xi0 ψ u y * commF σ JS JT xi0 ψ u y' := by
  unfold commF
  rw [← AddChar.map_add_eq_mul, GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right]
  congr 1; ring

theorem commF_zero_left (y : WOF F E nS nT) : commF σ JS JT xi0 ψ 0 y = 1 := by
  unfold commF
  rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one]

theorem commF_zero_right (u : WOF F E nS nT) : commF σ JS JT xi0 ψ u 0 = 1 := by
  unfold commF
  rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one]

theorem commF_neg_right (u y : WOF F E nS nT) : commF σ JS JT xi0 ψ u (-y) * commF σ JS JT xi0 ψ u y = 1 := by
  rw [← commF_add_right, neg_add_cancel, commF_zero_right]

theorem commF_swap (u y : WOF F E nS nT) : commF σ JS JT xi0 ψ y (-u) = commF σ JS JT xi0 ψ u y := by
  unfold commF
  have h1 := GlobalTheory.HeisThetaF.symplOHF_add_right (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) y (-u) u
  have h2 := GlobalTheory.HeisThetaF.symplOHF_add_left (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) (-u) u y
  rw [neg_add_cancel, GlobalTheory.HeisThetaF.symplOHF_zero_right] at h1
  rw [neg_add_cancel, GlobalTheory.HeisThetaF.symplOHF_zero_left] at h2
  congr 1
  linear_combination -h1 + h2

theorem commF_nsmul_left (u y : WOF F E nS nT) (n : ℕ) :
    commF σ JS JT xi0 ψ (n • u) y = commF σ JS JT xi0 ψ u y ^ n := by
  induction n with
  | zero => rw [zero_smul, commF_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, commF_add_left, ih, pow_succ]

theorem commF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : commF σ JS JT xi0 ψ x y = 1 := by
  unfold commF
  rw [symplOHF_half he hx hy, symplOHF_half he hy hx, sub_zero, AddChar.map_zero_eq_one]

theorem heisOF_add_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ (x + y) f = heisOF σ JS JT xi0 ψ x (heisOF σ JS JT xi0 ψ y f) := by
  rw [heisOF_heisOF, symplOHF_half he hx hy, AddChar.map_zero_eq_one, one_smul]

end GlobalTheory.SplitVacF

end

noncomputable section

namespace GlobalTheory.SplitVacF

open GlobalTheory.SplitInvFormF

end GlobalTheory.SplitVacF

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_local_unitNorm_vector_isotropic_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) := by
  first | exact @GlobalTheory.PlaneNorm.exists_local_unitNorm_vector | exact GlobalTheory.PlaneNorm.exists_local_unitNorm_vector | (intros; apply GlobalTheory.PlaneNorm.exists_local_unitNorm_vector <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES


theorem _root_.GlobalTheory.T.quasiInverseIsogeny_square_compat_comp_quasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ B₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] [GrpObj B₁] [IsCommMonObj B₁] (φ : A₁.left ⟶ A.left) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ → 0 < k → IsQuasiInv k ψ ψ' → IsQuasiInv k ψ₁ ψ₁' → IsGrpPullback A₁ A t φ → φ ≫ ψ.left = ψ₁.left ≫ θ → θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  first | (exact @GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv) | (exact GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv) | (intros; apply GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv  <;> assumption)
end
