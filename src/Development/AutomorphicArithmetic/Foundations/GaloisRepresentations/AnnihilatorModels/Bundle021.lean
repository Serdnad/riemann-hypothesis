module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle096
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section

open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Module CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison.Br

def LocFacts : Prop := ∀ (A : Type) [CommRing A] (a t : A), (∃ r : ℕ, a ∣ t ^ r) →
  (∀ x : Formalism.Per6.Loc2 a t, ∃ (r : ℕ) (y : A), Formalism.Per6.Loc2.mk₀ a t t ^ r * x = Formalism.Per6.Loc2.mk₀ a t y) ∧
    ∀ y : A, Formalism.Per6.Loc2.mk₀ a t y = 0 → ∃ r : ℕ, t ^ r * y = 0

def ActEq : Prop := ∀ (l : ℕ) [Fact l.Prime], (∀ (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (g : K.fixingSubgroup) (x : Acris l),
    galA g x = GroundTheory.PAdicHodge.ACris.galCris (Formalism.Per6.toBot g.1) x) ∧ ∀ z : ℤ_[l], Formalism.Per6.zB l z = Formalism.Per6.cB l (zA l z)

def PBTied : Prop := ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ K : FinExt l,
  ∃ (B : PB l K.1) (e : P.R.B ≃ₐ[ℚ_[l]] B.C), (∀ (g : ↥(GK K)) b, e (P.actQ (g : GQ l) b) = B.σ g (e b)) ∧ (∀ b, e (P.φB b) = B.φ (e b)) ∧
    Function.Injective B.φ

def AnnDrop : Prop := ∀ (F G B C : Type) [Field F] [Group G] [CommRing B] [Algebra F B] [CommRing C] [Algebra F C] (σ : G → End F B)
  (φ : B →ₐ[F] B) (s : G → (C →ₐ[F] C)) (ψ : C →ₐ[F] C) (e : B ≃ₐ[F] C), (∀ g b, e (σ g b) = s g (e b)) → (∀ b, e (φ b) = ψ (e b)) →
  Function.Injective ψ → ∀ (V : Type 1) [AddCommGroup V] [Module F V] (V₀ : Type) [AddCommGroup V₀] [Module F V₀] (i : V ≃ₗ[F] V₀)
    (act : G → End F V) (ρ : Representation F G V₀), (∀ g v, ρ g (i v) = i (act g v)) → ∀ (f q n N : ℕ) (A : Fin (n + 1) → End F V)
    (T : ℕ → End F V₀), (∀ (j : Fin (n + 1)) v, T j (i v) = i (A j v)) →
    (∀ x : V ⊗[F] C, (∀ g, TensorProduct.map (act g) (s g).toLinearMap x = x) →
      ∑ j : Fin (n + 1), ((-1) ^ (j : ℕ) * (q : ℤ) ^ ((j : ℕ).choose 2)) • TensorProduct.map (A j) (ψ.toLinearMap ^ (f * (n - j + N))) x = 0) →
    AnnD σ (φ.toLinearMap ^ f) q n ρ T

def FinAll : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  [IsDomain (OK l K)] [IsDiscreteValuationRing (OK l K)] (f : ℕ), 0 < f → Nat.card (IsLocalRing.ResidueField (OK l K)) = l ^ f →
  ∀ (ϖ : OK l K), Irreducible ϖ → ∀ (M : Model l K), M.Sm → ∀ (n j : ℕ) (T : Fin (n + 1) → Corr l M.X)
    (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p), PtId l (l ^ f) n (fn M.p ϖ) T →
  ∀ A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j), (∀ i, IsHk M (T i) (hr i) j (A i)) → ∀ B₀ : PB l K, ∃ N : ℕ, ∀ x, IsInv B₀ M j x →
    ∑ i : Fin (n + 1), ((-1) ^ (i : ℕ) * ((l ^ f : ℕ) : ℤ) ^ ((i : ℕ).choose 2)) •
      TensorProduct.map (A i) (B₀.φ.toLinearMap ^ (f * (n - i + N))) x = 0

def AnnModel : Prop := FinAll → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (K : FinExt l)
  [IsDomain (OK l K.1)] [IsDiscreteValuationRing (OK l K.1)] (f : ℕ), 0 < f → Nat.card (IsLocalRing.ResidueField (OK l K.1)) = l ^ f →
  ∀ (ϖ : OK l K.1), Irreducible ϖ → ∀ (M : Model l K.1), M.Sm → ∀ (n j : ℕ) (T : Fin (n + 1) → Corr l M.X)
    (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p), PtId l (l ^ f) n (fn M.p ϖ) T →
  ∀ A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j), (∀ i, IsHk M (T i) (hr i) j (A i)) →
  ∀ (V₀ : Type) [AddCommGroup V₀] [Module ℚ_[l] V₀] (i : M.V j ≃ₗ[ℚ_[l]] V₀) (ρ : Representation ℚ_[l] ↥(GK K) V₀),
    (∀ g v, ρ g (i v) = i (M.act j g v)) → ∀ T₀ : ℕ → End ℚ_[l] V₀, (∀ (a : Fin (n + 1)) v, T₀ a (i v) = i (A a v)) →
    AnnD (σCr P K) (ψCr P f) (l ^ f) n ρ T₀

end UpperTheory.Gal.crystallineComparison.Br
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem coe_bind (B : Multiset ℂˣ) :
    (do let a ← B; pure (a : ℂ) : Multiset ℂ) = B.map fun b : ℂˣ => (b : ℂ) := by
  show B.bind (fun b => {(b : ℂ)}) = _
  exact Multiset.bind_singleton B _

theorem UpperTheory.Gal.crystallineComparison.satGeom_of :
    SatGeom := by
  intro E Ω _ _ _ _ _ A w h a B
  have h0 : (0 : ℂ) ∉ B.map (fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ)) := by
    simp
  refine ⟨?_, ?_⟩
  · show ((WD.lpUnr h _).lpTw _).unr
    rw [WD.unr_tw]
    exact (WD.lpUnr_spec _ h0).1
  intro g hg
  show ((WD.lpUnr h _).lpTw _).charPol g = _
  unfold WD.lpUnr
  rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ, hg, coe_bind]
  have hsm : ∀ (s : ℂ) {ι : Type} (f : ι → ℂ), s • diagEnd f = diagEnd (fun i => s * f i) := by
    intro s ι f
    ext v i
    simp [diagEnd, mul_assoc]
  rw [hsm, charpoly_diagEnd, Finset.prod_eq_multiset_prod]
  set s : ℂ := (↑(normV w) ^ (((1 - (a : ℝ)) / 2 : ℝ) : ℂ)) ^ (-1 : ℤ) with hs
  refine (congrArg Multiset.prod (Multiset.map_univ (B.map (fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ)))
    (fun x => Polynomial.X - Polynomial.C (s * ↑(WD.unitOf x) ^ (-1 : ℤ))))).trans ?_
  unfold rootPol
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro b _
  simp only [Function.comp_apply]
  have hs' : s = (normV w : ℂ) ^ (((a : ℂ) - 1) / 2) := by
    rw [hs, zpow_neg_one, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [WD.coe_unitOf (Units.ne_zero _), Units.val_inv_eq_inv_val, zpow_neg_one, inv_inv, hs']
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.unrGeom_of :
    UnrOfGeom := by
  classical
  intro E Ω _ _ _ _ _ A w h x y hx hy g hg hxy
  obtain ⟨n, c, rfl⟩ := Unram.exists_diag hx
  obtain ⟨m, d, rfl⟩ := Unram.exists_diag hy
  rw [WD.charPol_mk, WD.charPol_mk, WDRep.diag_ρ, WDRep.diag_ρ, charpoly_diagEnd, charpoly_diagEnd, hg] at hxy
  have key := congrArg Polynomial.roots hxy
  simp only [Finset.prod_eq_multiset_prod] at key
  have R : ∀ {k : ℕ} (e : Fin k → ℂˣ),
      (Multiset.map (fun i => Polynomial.X - Polynomial.C (((e i : ℂˣ) : ℂ) ^ (-1 : ℤ))) Finset.univ.val).prod.roots =
        Finset.univ.val.map fun i => ((e i : ℂˣ) : ℂ) ^ (-1 : ℤ) := by
    intro k e
    have := Polynomial.roots_multiset_prod_X_sub_C
      (Finset.univ.val.map fun i => ((e i : ℂˣ) : ℂ) ^ (-1 : ℤ))
    rwa [Multiset.map_map] at this
  rw [R, R] at key
  apply Unram.diag_eq_diag
  have := congrArg (Multiset.map fun z : ℂ => z⁻¹) key
  simpa [Multiset.map_map, Function.comp_def, zpow_neg_one, inv_inv] using this
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem nil_transfer {R S M W : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup W] [Module S W] (φ : R →+* S) (mk : M → W) (hzero : mk 0 = 0)
    (hadd : ∀ x y, mk (x + y) = mk x + mk y) (hsmul : ∀ (a : R) x, mk (a • x) = φ a • mk x)
    (hext : ∀ f g : End S W, (∀ x, f (mk x) = g (mk x)) → f = g)
    (T : End S W) (D : End R M) (hTD : ∀ x, T (mk x) = mk (D x)) (Q : Polynomial R)
    (hQ : IsNilpotent (Polynomial.aeval D Q)) : IsNilpotent (Polynomial.aeval T (Q.map φ)) := by
  obtain ⟨N, hN⟩ := hQ
  have hpow : ∀ (n : ℕ) x, (T ^ n) (mk x) = mk ((D ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, hTD, ih]
  have key : ∀ (R' : Polynomial R) x,
      Polynomial.aeval T (R'.map φ) (mk x) = mk (Polynomial.aeval D R' x) := by
    intro R' x
    induction R' using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hq, hadd]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        End.mul_apply, End.mul_apply, hpow, Module.algebraMap_end_apply,
        Module.algebraMap_end_apply, hsmul]
  refine ⟨N, hext _ _ fun x => ?_⟩
  rw [← map_pow, ← Polynomial.map_pow, key, map_pow, hN]
  simp [hzero]

theorem UpperTheory.Gal.crystallineComparison.nilRho_of :
    NilRho := by
  intro l _ P ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj LL V _ _ _ _ _ ρ hV Q g
  haveI := hV.finite
  exact nil_transfer (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (wdMk P ι ρ) (wdMk_zero P ι ρ)
    (wdMk_add P ι ρ) (wdMk_smul P ι ρ) (fun _ _ => wd_ext P ι ρ) _ _
    (wdRho_mk P ι Bw h hj ρ g) Q
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

def CorrPull : Prop :=
  ∀ (l : ℕ) (S S' Y Y' : Scheme.{0}) (u : S' ⟶ S) (f : Y ⟶ S) (f' : Y' ⟶ S') (h : Y' ⟶ Y), IsPullback h f' f u →
    ∀ T : Corr l Y, T.r ≫ f = T.p ≫ f → ∃ (T' : Corr l Y') (g : T'.Z ⟶ T.Z),
      IsPullback T'.p g h T.p ∧ T'.r ≫ h = g ≫ T.r ∧ T'.r ≫ f' = T'.p ≫ f' ∧ T'.d = T.d

def PtIdBC : Prop :=
  ∀ (l q n : ℕ) (O O' : Type) [CommRing O] [CommRing O'] (σ : O →+* O'), σ.Flat → ∀ (ϖ : O) (ϖ' : O'),
    (∀ P : Ideal O', P.IsPrime → (σ ϖ ∈ P ↔ ϖ' ∈ P)) → (∀ a : O', a ^ q - a ∈ Ideal.span {ϖ'}) →
    ∀ (Y Y' : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of O)) (f' : Y' ⟶ Spec (CommRingCat.of O')) (h : Y' ⟶ Y),
    IsPullback h f' f (Spec.map (CommRingCat.ofHom σ)) → ∀ (T : Fin (n + 1) → Corr l Y) (T' : Fin (n + 1) → Corr l Y')
      (g : ∀ j, (T' j).Z ⟶ (T j).Z), (∀ j, IsPullback (T' j).p (g j) h (T j).p) → (∀ j, (T' j).r ≫ h = g j ≫ (T j).r) →
      (∀ j, (T' j).r ≫ f' = (T' j).p ≫ f') → PtId l q n (fn f ϖ) T → PtId l q n (fn f' ϖ') T'

def DvdOfNil : Prop :=
  ∀ (K W : Type) [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W] [Module.Finite K W] (M : End K W) (s : Multiset K) (u : K),
    u ≠ 0 → IsNilpotent (Polynomial.aeval M (Polynomial.C u * rootPol s)) → ∃ m : ℕ, M.charpoly ∣ rootPol s ^ m

def PhiKOfNil : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (a : ℕ)
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (LL : FinExt l) (r' : ↥(Dec (F := E) A) →* GL (Fin a) ↥LL.1),
    IsModel Bw r LL r' → Bw.IsCrysE P LL r' → ∀ (Q : Polynomial ↥LL.1), NilD (σSt P Bw.Kw) (ψSt P (resDeg l w)) (Bw.repE LL r') Q →
    ∀ (s : Multiset ℂ) (u : ℂ), u ≠ 0 → Q.map (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) = Polynomial.C u * rootPol s →
    ∃ g : ↥(Weil h), deg g = -1 ∧ ∃ m : ℕ, (wdAt P ι Bw h hj r).charPol g ∣ rootPol s ^ m

end UpperTheory.Gal.crystallineComparison
end
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct Module Matrix
open scoped Formalism.Per

namespace UpperTheory.Gal.crystallineComparison

def AffFinProj : Prop :=
  ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f → AffFin Y

theorem heckePol_map {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (q n : ℕ) (θ : ℕ → K) :
    (heckePol q n θ).map f = heckePol q n fun j => f (θ j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [heckePol, Polynomial.map_sum]

def AdmOfCrys : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → admitted (σCr P K) (finrank ℚ_[l] ↥(K0 K)) ρ

theorem admissible_of_crystalline : AdmOfCrys := by
  intro l _ P K V _ _ ρ h
  have e : Dinv (σCr P K) ρ = Dcris (P.PD K) ρ := by
    unfold Dinv Dcris actVB σCr
    refine iInf_congr fun g => ?_
    congr 3
    ext b
    simp [P.PD_actB]
  unfold admitted
  rw [e]
  exact h

end UpperTheory.Gal.crystallineComparison
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section Abstract

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

private theorem pow_restr (D S : Submodule L M) (hSD : S ≤ D) (T : End L D) (Φ : End L M)
    (hΦ : ∀ s ∈ S, Φ s ∈ S) (hT : ∀ s (hs : s ∈ S), ((T ⟨s, hSD hs⟩ : D) : M) = Φ s) (m : ℕ) :
    (∀ s ∈ S, (Φ ^ m) s ∈ S) ∧ ∀ s (hs : s ∈ S), (((T ^ m) ⟨s, hSD hs⟩ : D) : M) = (Φ ^ m) s := by
  induction m with
  | zero => exact ⟨fun s hs => hs, fun s hs => rfl⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [pow_succ', End.mul_apply]
      exact hΦ _ (ih1 s hs)
    · rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply]
      have e : (T ^ m) ⟨s, hSD hs⟩ = ⟨(Φ ^ m) s, hSD (ih1 s hs)⟩ := Subtype.ext (ih2 s hs)
      rw [e, hT _ (ih1 s hs)]

private theorem aeval_restr (D S : Submodule L M) (hSD : S ≤ D) (T : End L D) (Φ : End L M)
    (hΦ : ∀ s ∈ S, Φ s ∈ S) (hT : ∀ s (hs : s ∈ S), ((T ⟨s, hSD hs⟩ : D) : M) = Φ s) (Q : Polynomial L) :
    (∀ s ∈ S, Polynomial.aeval Φ Q s ∈ S) ∧
      ∀ s (hs : s ∈ S), ((Polynomial.aeval T Q ⟨s, hSD hs⟩ : D) : M) = Polynomial.aeval Φ Q s := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [map_add (f := _), LinearMap.add_apply]
      exact add_mem (hp.1 s hs) (hq.1 s hs)
    · rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hp.2 s hs, hq.2 s hs]
  | monomial n a =>
    obtain ⟨h1, h2⟩ := pow_restr D S hSD T Φ hΦ hT n
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [Polynomial.aeval_monomial, End.mul_apply, Module.algebraMap_end_apply]
      exact S.smul_mem a (h1 s hs)
    · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, End.mul_apply, End.mul_apply,
        Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul, h2 s hs]

private theorem aeval_commute {D : Type} [AddCommGroup D] [Module L D] (T m : End L D) (h : Commute T m)
    (Q : Polynomial L) : Commute (Polynomial.aeval T Q) m := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_left hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact Commute.mul_left (show Commute _ m from Algebra.commutes a m) (h.pow_left n)

private theorem nil_abs {U : Type} (D S : Submodule L M) (hSD : S ≤ D) (T : End L D) (Φ : End L M)
    (hΦ : ∀ s ∈ S, Φ s ∈ S) (hT : ∀ s (hs : s ∈ S), ((T ⟨s, hSD hs⟩ : D) : M) = Φ s) (Q : Polynomial L) (N : ℕ)
    (hN : ∀ s ∈ S, (Polynomial.aeval Φ Q ^ N) s = 0) (m : U → End L D) (mV : U → End L M)
    (hm : ∀ c (x : D), ((m c x : D) : M) = mV c x) (hc : ∀ c, T * m c = m c * T)
    (hcl : ∀ x : D, (x : M) ∈ AddSubgroup.closure {y | ∃ (c : U) (s : M), s ∈ S ∧ y = mV c s}) :
    IsNilpotent (Polynomial.aeval T Q) := by
  obtain ⟨a1, a2⟩ := aeval_restr D S hSD T Φ hΦ hT Q
  obtain ⟨-, b2⟩ := pow_restr D S hSD _ _ a1 a2 N
  have hkill : ∀ s (hs' : s ∈ S), (Polynomial.aeval T Q ^ N) ⟨s, hSD hs'⟩ = 0 := by
    intro s hs'
    refine Subtype.ext ?_
    rw [b2 s hs']
    exact hN s hs'
  have hcomm : ∀ c, Commute (Polynomial.aeval T Q ^ N) (m c) := fun c =>
    Commute.pow_left (aeval_commute _ _ (hc c) Q) N
  have key : ∀ y, y ∈ AddSubgroup.closure {y | ∃ (c : U) (s : M), s ∈ S ∧ y = mV c s} →
      ∃ hy : y ∈ D, (Polynomial.aeval T Q ^ N) ⟨y, hy⟩ = 0 := by
    intro y hy
    refine AddSubgroup.closure_induction
      (p := fun y _ => ∃ hy : y ∈ D, (Polynomial.aeval T Q ^ N) ⟨y, hy⟩ = 0)
      ?_ ⟨zero_mem _, map_zero _⟩ ?_ ?_ hy
    · rintro _ ⟨c, s, hs', rfl⟩
      have e : mV c s = ((m c ⟨s, hSD hs'⟩ : D) : M) := (hm c ⟨s, hSD hs'⟩).symm
      refine ⟨e ▸ (m c ⟨s, hSD hs'⟩).2, ?_⟩
      have h1 := LinearMap.congr_fun (hcomm c).eq ⟨s, hSD hs'⟩
      rw [End.mul_apply, End.mul_apply, hkill s hs', map_zero] at h1
      have h2 : (⟨mV c s, e ▸ (m c ⟨s, hSD hs'⟩).2⟩ : D) = m c ⟨s, hSD hs'⟩ := Subtype.ext e
      rw [h2]; exact h1
    · rintro a b _ _ ⟨ha, ea⟩ ⟨hb, eb⟩
      refine ⟨add_mem ha hb, ?_⟩
      have := map_add (Polynomial.aeval T Q ^ N) ⟨a, ha⟩ ⟨b, hb⟩
      rw [ea, eb, add_zero] at this
      exact this
    · rintro a _ ⟨ha, ea⟩
      refine ⟨neg_mem ha, ?_⟩
      have := map_neg (Polynomial.aeval T Q ^ N) ⟨a, ha⟩
      rw [ea, neg_zero] at this
      exact this
  refine ⟨N, LinearMap.ext fun x => ?_⟩
  obtain ⟨hy, e⟩ := key x.1 (hcl x)
  exact e

end Abstract

theorem UpperTheory.Gal.crystallineComparison.nilWeil_of :
    NilWeil := by
  intro l _ P E Ω _ _ _ _ _ A w h O _ _ _ Bw hj LL V _ _ _ _ _ ρ hV hs Q hN g hg
  haveI := hV.finite
  obtain ⟨N, hN⟩ := hN
  have hSD : Dst P ρ ≤ Dpst P ρ := fun s hs =>
    (mem_Dpst P ρ).mpr ⟨Bw.Kw, fun g _ => (mem_Dst P ρ).mp hs g⟩
  have hΦ : onPer (ψSt P (resDeg l w)) ↥LL.1 V = phiV P ↥LL.1 V ^ resDeg l w := by
    change onB P ↥LL.1 V ((phiSt P).toLinearMap ^ resDeg l w) = _
    rw [map_pow]; rfl
  have hpow : ∀ (m : ℕ) (x : ↥(Dpst P ρ)),
      (((phiD P ρ ^ m) x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = (phiV P ↥LL.1 V ^ m) x := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih =>
      intro x
      rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, coe_phiD, ih]
  have hst : ∀ (m : ℕ), ∀ s ∈ Dst P ρ, (phiV P ↥LL.1 V ^ m) s ∈ Dst P ρ := by
    intro m s hs'
    refine (mem_Dst P ρ).mpr fun k => ?_
    have hc : Commute (phiV P ↥LL.1 V ^ m) (stRep P ρ k) := Commute.pow_left (phiV_stRep P ρ k) m
    have := LinearMap.congr_fun hc.eq s
    rw [End.mul_apply, End.mul_apply, (mem_Dst P ρ).mp hs' k] at this
    exact this.symm
  have hW : ∀ s (hs' : s ∈ Dst P ρ), ((weilD Bw h P ρ g ⟨s, hSD hs'⟩ : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
      onPer (ψSt P (resDeg l w)) ↥LL.1 V s := by
    intro s hs'
    have e : -alpha l g = ((resDeg l w : ℕ) : ℤ) := by rw [alpha, hg]; ring
    rw [weilD_apply, e, zpow_natCast, Units.val_pow_eq_pow_val, coe_phiU, End.mul_apply, coe_actD, hpow, hΦ]
    exact (mem_Dst P ρ).mp (hst _ s hs') _
  have hΦS : ∀ s ∈ Dst P ρ, onPer (ψSt P (resDeg l w)) ↥LL.1 V s ∈ Dst P ρ := by
    intro s hs'
    rw [hΦ]; exact hst _ s hs'
  have hcl := mem_closure_mulV_of_finrank_eq l P Bw.Kw LL V ρ hV (Dst P ρ) le_rfl
    (fun c hc x hx => (mem_Dst P ρ).mpr fun k => by
      rw [← Module.End.mul_apply, stRep_mulV P ρ k c c (mem_GK.mp k.2 _ hc), Module.End.mul_apply,
        (mem_Dst P ρ).mp hx k]) hs
  exact nil_abs (Dpst P ρ) (Dst P ρ) hSD (weilD Bw h P ρ g) (onPer (ψSt P (resDeg l w)) ↥LL.1 V) hΦS hW Q N
    (fun s hs' => hN s hs') (mulD P ρ) (mulV P ↥LL.1 V) (fun _ _ => rfl) (weilD_mulD Bw h P ρ hj g) (fun x => hcl x.1 x.2)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem charPol_wdPst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (LL : FinExt l)
    {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (hV : IsPst P ρ) (g : ↥(Weil h)) :
    haveI := hV.finite
    (wdPst P ι Bw h hj ρ).charPol g = (wdRho P ι Bw h hj ρ g).charpoly := by
  have := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, WD.charPol_mk]
  obtain ⟨u, -, hu, -, hc, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  exact (GlobalTheory.WeilDeligne.isFrobSS_of_unipotent u hu hc hρ).charpoly_eq g

theorem UpperTheory.Gal.crystallineComparison.wdModel_of :
    WdModel := by
  intro l _ P ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r LL r' hm hV g
  have key : wdAt P ι Bw h hj r = wdPst P ι Bw h hj (Bw.repE LL r') := by
    obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj (r := r) ⟨LL, r', hm, hV⟩
    have h₁ : L₁.1 ≤ (supExt L₁ LL).1 := le_sup_left
    have h₂ : LL.1 ≤ (supExt L₁ LL).1 := le_sup_right
    have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
        mapRep (IntermediateField.inclusion h₂).toRingHom r' := by
      ext x i j
      exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f x : Matrix (Fin a) (Fin a) (Om l)) i j)
        (hm₁.2.trans hm.2.symm)
    rw [e₁, GlobalTheory.Pst.BridgeParam.wdPst_enlarge P ι Bw h hj h₁ r₁ hV₁,
      GlobalTheory.Pst.BridgeParam.wdPst_enlarge P ι Bw h hj h₂ r' hV, e]
  refine ⟨?_, ?_⟩
  · rw [key]
    exact charPol_wdPst P ι h Bw hj LL (Bw.repE LL r') hV g
  · exact (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw LL _ _ hV).trans (by simp)
end
