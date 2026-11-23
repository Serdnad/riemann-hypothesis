module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
public import ReciprocityTheory.DualLattices.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle048
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle053
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle052
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ChSplit
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.lattice_second_goodness : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → (∀ τ, LocFree R (r τ) (D.kerH R p τ (χ τ)) ∧ ∀ i, LocFree R 1 (D.dId R p (χ τ) i) ∧ LocFree R 1 ((D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _))) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → (D.bc RC).Good₂ RC p (fun τ a => algebraMap Ω C (χ τ a)) ∧ ∀ τ, (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.kerH R p τ (χ τ)) ∧ ∀ i, (D.bc RC).dId RC p (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) ∧ ((D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i).comap (AddMonoidHom.inl _ _) = spanOver RC (algebraMap Ω C '' (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.main | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.main <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

theorem _root_.GlobalTheory.T.hodge_kernel_image_lattice : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (τ : Sg), w ≠ 0 → mulLat w (stdLat RC _) ≤ D.af RC p (χ τ) → D.af RC p (χ τ) ≤ stdLat RC _ → ∀ (ht : (Fin n → C) →ₗ[C] (Fin (s τ) → C)) (hb : (Fin (r τ) → C) →ₗ[C] (Fin n → C)), Function.Injective hb → LinearMap.range hb = LinearMap.ker ht → (stdLat RC _).map ht.toAddMonoidHom = D.omHT τ → (stdLat RC _).comap hb.toAddMonoidHom = D.W τ → (D.hh RC p (χ τ)).map ht.toAddMonoidHom = D.om τ → (D.hh RC p (χ τ)).comap hb.toAddMonoidHom = divLat w (D.lie τ) → (∀ b c, (b, c) ∈ D.Del τ ↔ w • b ∈ stdLat RC _ ∧ c - ht b ∈ D.omHT τ) → (∀ a b, (a, b) ∈ D.Gam τ ↔ w • a ∈ D.W τ ∧ b - hb a ∈ stdLat RC _) → D.imH RC p τ (χ τ) = D.om τ ∧ D.kerH RC p τ (χ τ) = divLat w (D.lie τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PtSeq.pt_seq_lin | exact GlobalTheory.CompanionTheory.Ar.PtSeq.pt_seq_lin | (intros; apply GlobalTheory.CompanionTheory.Ar.PtSeq.pt_seq_lin <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tensor_product_hopf_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), ∃ AA : HopfOrder (C := C) R (N₁ × N₂), AA.carrier = tens A₁.carrier A₂.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (z.1, 0)) ∈ AA.carrier) ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (0, z.2)) ∈ AA.carrier) ∧ ∀ c₁ c₂, HasColen R v A₁.carrier c₁ → HasColen R v A₂.carrier c₂ → HasColen R v AA.carrier (c₁ ^ Fintype.card N₂ * c₂ ^ Fintype.card N₁) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tensor_product_hopf_orders | exact GlobalTheory.CompanionTheory.Relay.tensor_product_hopf_orders | (intros; apply GlobalTheory.CompanionTheory.Relay.tensor_product_hopf_orders <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

theorem _root_.GlobalTheory.T.dual_tower_hodge_tate_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) {R₀ : Type} [CommRing R₀] (g : ℕ) (B : BX R₀) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) [Algebra (Tw.O : Type) C], v.Integers (Tw.O : Type) → v (p : C) < 1 → ∀ [Algebra ℤ_[p] (Tw.O : Type)] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : (Tw.O : Type)) (D : Dat p g B Tw Dt Oe σ cp) (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (G' : Over (Spec (CommRingCat.of (Tw.O : Type)))) [GrpObj G'] [IsCommMonObj G'] (ψ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (Tw.O : Type)))) ψ → ∃ pt : Nb p g → (sp (R₀ := (Tw.O : Type)) (Tw.O : Type) ⟶ G'), (∀ t, (pt t).left ≫ ψ = (e Tw.O (ptOf B D.L.τ t)).left) ∧ IsTorsPts G' p pt ∧ ∀ T : TorsRep G' p, D.evImg C = torsFun C T pt := by
  first | exact @GlobalTheory.CompanionTheory.Relay.dual_tower_hodge_tate_datum | exact GlobalTheory.CompanionTheory.Relay.dual_tower_hodge_tate_datum | (intros; apply GlobalTheory.CompanionTheory.Relay.dual_tower_hodge_tate_datum <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv

theorem beta_rhoH_eq : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O]
    [StarRing O] (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)),
    beta B p (rhoH B a y) = ((rho B (star a)).transpose.map (· ^ p)).mulVec (beta B p y) := by
  intro R _ p _ _ d O _ _ B a y
  refine dotProduct_eq _ _ fun u => ?_
  have hadj := (GlobalTheory.T.formal_hermitian_action_pairing R d O B).2.2 (star a) (alpha B p u) y
  rw [star_star] at hadj
  have htw := GlobalTheory.T.alpha_equivariant_frobenius R p d O B (star a) u
  rw [dotProduct_comm, dotProduct_beta, ← hadj, ← htw, ← dotProduct_beta, dotProduct_comm _ (beta B p y),
    Matrix.dotProduct_mulVec, Matrix.transpose_map, Matrix.mulVec_transpose]

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.formal_group_action_ring_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ ρ : O →+* Matrix (Fin d) (Fin d) R, ∀ a, ρ a = rho B a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.rho_hom | exact GlobalTheory.CompanionTheory.Ar.Conj.rho_hom | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.rho_hom <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.degree_mono_lattice_le : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le | exact GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.short_exact_sub_degree_bound : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (X : Submodule K V'), IsBun C L' → ShortExact C L L' L'' f g → subDeg C L' X ≤ subDeg C L (X.comap f) + subDeg C L'' (X.map g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes.subDeg_ses | exact GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes.subDeg_ses | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes.subDeg_ses <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.sub_degree_mono_injective_hom : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_map_of_injective | exact GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_map_of_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_map_of_injective <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

theorem _root_.GlobalTheory.T.sub_degree_nonpos_trivial_lattice : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_zero_of_trivial | exact GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_zero_of_trivial | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_zero_of_trivial <;> assumption)
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem degree_eq_sum_eigen : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → deg C L = ∑ s, subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) :=
  @PositivityTheory.HtPt.Ch.split_deg

end GlobalTheory.CompanionTheory.Ar.Crv
end

section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem eigen_ses_subDeg : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ (ρ : O → V →ₗ[K] V) (ρ' : O →+* Module.End K V') (ρ'' : O → V'' →ₗ[K] V''), IsBun C L' → (∀ a, IsHom C L' L' (ρ' a)) → ShortExact C L L' L'' f g → (∀ a x, f (ρ a x) = ρ' a (f x)) → (∀ a y, g (ρ' a y) = ρ'' a (g y)) → ∀ s, subDeg C L' (eig (fun a => ρ' a) (fun a => algebraMap k K (χ s a))) = subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) + subDeg C L'' (eig (fun a => ρ'' a) (fun a => algebraMap k K (χ s a))) :=
  @PositivityTheory.HtPt.Ch.split_ses

end GlobalTheory.CompanionTheory.Ar.Crv
end
