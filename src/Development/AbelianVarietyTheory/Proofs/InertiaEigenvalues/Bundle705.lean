module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle025
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle339
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCMValueHeckeCharacterAuxiliarySetOfEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle645
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle433
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle049
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle060
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisLogTeichmullerAssociatedSubOneOnDisc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle199
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT

namespace GlobalTheory.SphSupport

theorem toral_of_isSpherical (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k))
    (hs : IsSpherical x.rep) :
    ∃ s, HasSupport x.rep s ∧ ∀ y ∈ s, ∃ (χ : kˣ →* ℂˣ) (hχ : IsUnram χ), y = IrrGL.ofChar χ
      (isSmoothChar_of_isUnram hχ) := by
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i =>
    isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have H : IsCuspSupport x.rep (fun _ : Fin x.1 => 1) fun a => detRep (Fin 1) (unrChar k (α a)) :=
    ⟨x.2.rep.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      hα.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k x.1 fun i => unrChar k (α i))⟩
  refine ⟨_, hasSupport_of_isCuspSupport H, ?_⟩
  intro y hy
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), rfl⟩

theorem toral_and_good_of_isSpherical : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)),
      IsSpherical x.rep → Toral x ∧ Good x := by
  intro hBZ k _ _ _ _ x hs
  obtain ⟨s, hsup, hs1⟩ := toral_of_isSpherical hBZ k x hs
  have h1 : ∀ y ∈ s, y.1 = 1 := fun y hy => by
    obtain ⟨χ, -, rfl⟩ := hs1 y hy
    rfl
  exact ⟨⟨s, hsup, h1⟩, ⟨s, hsup, fun y hy => Or.inl (h1 y hy)⟩⟩

end GlobalTheory.SphSupport
end

section

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.SerLocal

variable (D : D7)

theorem inePol_zero (w : PlE D.host) (s) (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (D.naut.lpZero w) s = 1 := by
  rw [((D.naut.unr_iff_ine _).1 (D.naut.lpZero_unr w)).2 s hs, D.naut.lpDim_zero, pow_zero]

theorem inePol_foldr {ι : Type} {w : PlE D.host} (F : ι → D.naut.LP w) (l : List ι) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (l.foldr (fun x acc => D.naut.lpSum (F x) acc) (D.naut.lpZero _)) s =
      (l.map fun x => D.naut.inePol (F x) s).prod := by
  induction l with
  | nil => simpa using inePol_zero D w s hs
  | cons x l ih => rw [List.foldr_cons, D.naut.inePol_sum, ih, List.map_cons, List.prod_cons]

theorem inePol_speh (p : Part D.naut.CG) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (spehLoc D.nd D.naut p w) s = D.naut.inePol (D.naut.locG p.π w) s ^ p.d := by
  have e : spehLoc D.nd D.naut p w = (List.range p.d).foldr (fun (j : ℕ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - j)) acc) (D.naut.lpZero w) := by
    simp only [spehLoc, bind_pure_comp, List.map_eq_map, List.foldr_map]
  rw [e, inePol_foldr D (fun k : ℕ => D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) _ s hs]
  simp [D.naut.inePol_tw _ _ s hs]

theorem inePol_iso (P : List (Part D.naut.CG)) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut P w) s =
      (P.map fun p => D.naut.inePol (D.naut.locG p.π w) s ^ p.d).prod := by
  rw [isoLoc, inePol_foldr D (fun p => spehLoc D.nd D.naut p w) _ s hs]
  simp only [inePol_speh D _ w s hs]

theorem inePol_twist (hU : IneUnr D) (i : D.nd.Loc) (Sig : List (Part D.naut.CG)) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut
      (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) w) s =
      D.naut.inePol (isoLoc D.nd D.naut Sig w) s * D.naut.inePol (D.naut.locG (D.naut.muC i) w) s ^ D.R.t := by
  rw [inePol_iso D _ w s hs, inePol_iso D _ w s hs, twistIso, List.map_map]
  have e : ∀ {a} (π : D.naut.CG a), D.naut.inePol (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) s =
      D.naut.inePol (D.naut.locG π w) s := fun π => by
    rw [D.naut.locG_tw]
    exact hU w _ _ (D.naut.locG_dim _ w) (D.naut.etaTinv_def w).1 s hs
  simp [Function.comp_def, e, muPart]

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem eq_of_rootsBar_eq {f f' : (ZMod g)[X]} (hf : f.Monic) (hf' : f'.Monic)
    (h : Formalism.CyclotomicNorms.rootsBar f = Formalism.CyclotomicNorms.rootsBar f') : f = f' := by
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (f'.map _)).eq_prod_roots_of_monic (hf'.map _)]
  exact congrArg (fun m => (Multiset.map (fun x => X - C x) m).prod) h

theorem rootsBar_pow (c : ZMod g) (t : ℕ) :
    Formalism.CyclotomicNorms.rootsBar ((X - C c) ^ t) = t • {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c} := by
  rw [Formalism.CyclotomicNorms.rootsBar, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, roots_pow, roots_X_sub_C]

theorem eq_of_teich (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (hτ : Function.Injective τ) {f f' : (ZMod g)[X]} (hf : f.Monic)
    (hf' : f'.Monic) (c : ZMod g) (t : ℕ)
    (h : ((Formalism.CyclotomicNorms.rootsBar (f * (X - C c) ^ t)).map fun x => X - C (τ x)).prod =
      ((Formalism.CyclotomicNorms.rootsBar f').map fun x => X - C (τ x)).prod *
        (X - C (τ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c))) ^ t) : f = f' := by
  have h0 : f * (X - C c) ^ t ≠ 0 := (hf.mul ((monic_X_sub_C c).pow t)).ne_zero
  have hm : Formalism.CyclotomicNorms.rootsBar (f * (X - C c) ^ t) = Formalism.CyclotomicNorms.rootsBar f + Formalism.CyclotomicNorms.rootsBar ((X - C c) ^ t) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.map_mul, roots_mul]
    rw [← Polynomial.map_mul]
    exact Polynomial.map_ne_zero h0
  rw [hm, rootsBar_pow, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_nsmul, Multiset.prod_nsmul,
    Multiset.map_singleton, Multiset.prod_singleton] at h
  have h2 := mul_right_cancel₀ (pow_ne_zero t (X_sub_C_ne_zero _)) h
  have h3 := congrArg Polynomial.roots h2
  have e : ∀ m : Multiset (Formalism.CyclotomicNorms.Fbar g),
      ((m.map fun x => X - C (τ x)).prod).roots = m.map τ := fun m => by
    rw [← roots_multiset_prod_X_sub_C (m.map τ), Multiset.map_map]; rfl
  rw [e, e] at h3
  exact eq_of_rootsBar_eq hf hf' (Multiset.map_injective hτ h3)

end Roots

theorem serLoc : ∀ (D : D7) (S : ∀ k, @Sys (D.host.g k) ⟨D.host.g_prime k⟩),
    (∀ k f, D.ntypes.eSer k f = @Sys.e _ ⟨D.host.g_prime k⟩ (S k) D.R.r f) → IneUnr D → LocType D S →
    SerLoc D := by
  intro D S hS hU hL i σ' k v f F hF hne
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hex : ∃ P Sig, (∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) ∧
      IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) ∧
      ∃ F' ∈ D.naut.typeV i P,
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f)) F' ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hne
    rw [D.mtpar_tie i σ'] at hF
    have hle : (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) ∧
        IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv)},
        D.naut.typeV i P) ≤
        LinearMap.ker (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f))) :=
      iSup₂_le fun P ⟨Sig, h1, h2⟩ F' hF' => hno P Sig h1 h2 F' hF'
    exact hle hF
  obtain ⟨P, Sig, hSig, hBC, F', hF', hne'⟩ := hex
  obtain ⟨π, χ, c, h1, h2, h3, h4⟩ := hL i P k v
  obtain ⟨u, hu, hu'⟩ := h1 F' hF' (D.ntypes.eSer k f)
    (Subalgebra.mem_center_iff.2 fun b => (D.ntypes.eSer_central k f b).symm) hne'
  rw [hS] at hu'
  have hmon : f.Monic := ((S k).label D.R.r f (fun h0 => hu' (by rw [h0]; simp [actTop]))).1
  have hHas := GlobalTheory.T.hasSeriesVector_mul_of_parahoricBlockCharVector _ (S k) _ _ π.ρ D.R.r D.R.t χ _ f u rfl h2 hu hu'
  have h5 := h4 _ hHas
  have hs := D.ntypes.tg_mem k v
  rw [← hBC.2.2.2.1 _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v), inePol_twist D hU i Sig _ _ hs, hSig, h3,
    D.ntypes.inertiaCharpoly_type k v _ (by
      rw [← D.ntypes.labPar_def, (D.ntypes.labPar_monic k σ' v).2, D.ntypes.locPar_dim]),
    ← D.ntypes.labPar_def] at h5
  exact eq_of_teich _ (GlobalTheory.TameLabels.teich_injective _ (D.ntypes.teichC_inj k)) hmon (D.ntypes.labPar_monic k σ' v).1 c _ h5.symm

end GlobalTheory.SerLocal
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.mem_unramifiedField_of_mem_maxUnramified_sup_root : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (n : ℕ) (x : Om l), x ∈ MaximalUnramifiedExtension l → x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} → x ∈ Kunr l a := by
  first | exact @GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup | exact GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup | (intros; apply GlobalTheory.KunrDisj.mem_Kunr_of_mem_Kur_of_mem_sup <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie GlobalTheory.ToricRational GlobalTheory.ToricDistribution

namespace GlobalTheory.LamTie

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_th_of (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hG : RatioConj) (hL : ToricSumFormula) {i : X.Tw} {ι : ℂ →+* Kbar X i}
    (hE : ∀ (σ : D.host.E →+* ℂ) (x : D.host.E), ι (σ x) ∈ (algebraMap (FractionRing (X.O i)) (Kbar X i)).range)
    {lam : X.abelian₂ i} {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF D.host.E)} {χ : HChar D.host.E}
    (hD : IsHostDatum D.host φ s κ 𝔣 χ) (h𝔣 : ∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i)
    (hX : ∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (χ.val P : ℂ) = 1) :
    ∃ t : ∀ Q, X.RCG i Q → FractionRing (X.O i), ∀ th : ∀ i Q, X.abelian₂ i → X.RCG i Q → FractionRing (X.O i),
      (∀ Q, th i Q lam = t Q) → IsThOf (setTh X th) i ι lam φ s κ 𝔣 χ := by
  obtain ⟨T₀, hT₀, h0⟩ := exists_toricSum_ne_zero hL host_unramFin hD
  have := X.O_complete i
  have key : ∀ Q, ∃ t : X.RCG i Q → FractionRing (X.O i), BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
      ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
        IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
        ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (t δ) = (ι T₀)⁻¹ * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q) := fun Q => by
    by_cases hQ : BlochKatoReduction.Gen.QOk X i Q
    · obtain ⟨hfin, T, hT⟩ := exists_classTerms hL host_unramFin hD (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1
      obtain ⟨π, hπ, hπl⟩ := exists_isRecMap hA hQ 𝔣
      choose t ht using partialSum_mem hA hG host_unramFin hD (X.resO_ac i) (X.lPrime i).out.ne_zero (X.O_l i) ι hE (X.S0 i)
        (fun P hP => ⟨(algebraMap (X.O i) _ (X.Xv i lam P))⁻¹, by
          rw [map_inv₀, ← IsScalarTower.algebraMap_apply]
          exact (eq_inv_of_mul_eq_one_right (hX P hP)).symm⟩) hT₀ h0 (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1 hT π hπl
      exact ⟨t, fun _ => ⟨hfin, π, T, hπ, hT, ht⟩⟩
    · exact ⟨0, fun h => absurd h hQ⟩
  choose t ht using key
  refine ⟨t, fun th e => ⟨(ι T₀)⁻¹, inv_ne_zero ((map_ne_zero ι).2 h0), fun Q hQ => ?_⟩⟩
  obtain ⟨h1, π, T, h2, h3, h4⟩ := ht Q hQ
  exact ⟨h1, π, T, h2, h3, fun δ => (congrArg _ (congrFun (e Q) δ)).trans (h4 δ)⟩

end GlobalTheory.LamTie
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.DualTwistCrys

theorem crys_chi (D : D7) (i : D.nd.Loc) (hChi : GlobalTheory.PtCore.ChiOneE D i) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) := hChi w hw C.LL C.le

theorem card_emb (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
  have := D.nd.lPrime i
  have := C.LL.2
  have := (D.nbr i w hw).Kw.2
  have h2 := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw C.LL (fun τ y => C.le
    ((D.nbr i w hw).LL_split τ y)) inferInstance).2
  rw [Nat.card_eq_fintype_card, h2]

theorem twist_crys (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (hchi : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (hcC : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) := by
  have := D.nd.lPrime i
  have := C.LL.2
  refine (GlobalTheory.TwistRepCrys.isCrys_and_multV_twist (D.nd.l i) (D.loc _) (D.locA _) (D.locT _)
    (D.nbr i w hw).Kw C.LL _ (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) _
    (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹
    ⟨LinearEquiv.refl _ _, fun g v => ?_⟩ hchi hcC).1
  rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply, GlobalTheory.TateDualCrys.matRep_apply,
    GlobalTheory.TateDualCrys.matRep_apply]
  exact Matrix.smul_mulVec _ _ _

theorem crys_coef (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (hcw : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact GlobalTheory.CrysCoef.isCrys_inclusion (D.nd.l i) (D.loc _) (D.nbr i w hw).Kw (D.nbr i w hw).LL C.LL C.le _ _ hcw

theorem dual_crys (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (htw : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) := by
  have := D.nd.lPrime i
  exact (GlobalTheory.TateDualCrys.tateDual (D.locT _) (D.nbr i w hw).Kw C.LL (card_emb D i w hw C) _ _
    (GlobalTheory.TateDualCrys.loc_rDuO D i w hw C.LL C.le r x) htw).1

theorem tw_crys (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (x : D.nd.X i)
    (hchi : IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹))
    (hcC : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)))) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) := by
  rw [← GlobalTheory.AmbientDual.twist_locC]
  exact twist_crys D i r w hw C x hchi hcC

end GlobalTheory.DualTwistCrys
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.acris_log_teichmuller_associated_sub_one_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) → Associated (γ C.t) (bk.iA (mu C.ε)) := by
  first | exact @GlobalTheory.BSP.SeedT.t_assoc_mu | exact GlobalTheory.BSP.SeedT.t_assoc_mu | (intros; apply GlobalTheory.BSP.SeedT.t_assoc_mu <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.HomDefect

theorem smul_cancel {R : Type} [CommRing R] {m n : Type} {r : R} (hr : r ∈ nonZeroDivisors R)
    {M N : Matrix m n R} (h : r • M = r • N) : M = N := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact (mul_cancel_left_mem_nonZeroDivisors hr).1 this

theorem map_smul' {R R' : Type} [CommRing R] [CommRing R'] {m n : Type} (φ : R →+* R') (c : R)
    (M : Matrix m n R) : (c • M).map φ = φ c • M.map φ := by
  ext i j; simp

theorem map_frob {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {B : Obj l ↥(OL K)} (f : Hom bk.prism B)
    {m n : Type} (M : Matrix m n bk.S) : (M.map (frobS l bk.a)).map (BK.hf f) = (M.map (BK.hf f)).map B.D.φ := by
  ext i j
  exact f.f_φ (M i j)

end GlobalTheory.BSP.HomDefect



open GlobalTheory.BSP.HomDefect in
theorem GlobalTheory.BSP.strat_homDefect_φ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S), bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * (S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g).map B.D.φ) = BK.hf f bk.E ^ S'.a • ((S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g) * S.A.map (BK.hf g)) := by
  intro l _ K bk d d' S S' Y hY B f g
  obtain ⟨hfE, -, -⟩ := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g
  obtain ⟨hgE, -, -⟩ := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B g f
  have hYf := congrArg (fun M => M.map (BK.hf f)) hY
  have hYg := congrArg (fun M => M.map (BK.hf g)) hY
  simp only [map_smul', Matrix.map_mul, map_pow, map_frob] at hYf hYg
  have e1 := S.ε_φ f g
  have e2 := S'.ε_φ f g
  have T1 : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * ((S'.ε f g).map B.D.φ * (Y.map (BK.hf g)).map B.D.φ)) =
      BK.hf f bk.E ^ S'.a • (S'.ε f g * Y.map (BK.hf g) * S.A.map (BK.hf g)) := by
    apply smul_cancel (pow_mem hgE S'.a)
    calc BK.hf g bk.E ^ S'.a • BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * ((S'.ε f g).map B.D.φ * (Y.map (BK.hf g)).map B.D.φ))
        = BK.hf g bk.E ^ S.a • ((BK.hf g bk.E ^ S'.a • (S'.A.map (BK.hf f) * (S'.ε f g).map B.D.φ)) * (Y.map (BK.hf g)).map B.D.φ) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = BK.hf g bk.E ^ S.a • ((BK.hf f bk.E ^ S'.a • (S'.ε f g * S'.A.map (BK.hf g))) * (Y.map (BK.hf g)).map B.D.φ) := congrArg (fun M => BK.hf g bk.E ^ S.a • (M * (Y.map (BK.hf g)).map B.D.φ)) e2
      _ = BK.hf f bk.E ^ S'.a • (S'.ε f g * (BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf g) * (Y.map (BK.hf g)).map B.D.φ))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = BK.hf f bk.E ^ S'.a • (S'.ε f g * (BK.hf g bk.E ^ S'.a • (Y.map (BK.hf g) * S.A.map (BK.hf g)))) := congrArg (fun M => BK.hf f bk.E ^ S'.a • (S'.ε f g * M)) hYg
      _ = BK.hf g bk.E ^ S'.a • BK.hf f bk.E ^ S'.a • (S'.ε f g * Y.map (BK.hf g) * S.A.map (BK.hf g)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
  have T2 : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * ((Y.map (BK.hf f)).map B.D.φ * (S.ε f g).map B.D.φ)) =
      BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * S.ε f g * S.A.map (BK.hf g)) := by
    apply smul_cancel (pow_mem hfE S.a)
    calc BK.hf f bk.E ^ S.a • BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * ((Y.map (BK.hf f)).map B.D.φ * (S.ε f g).map B.D.φ))
        = BK.hf g bk.E ^ S.a • ((BK.hf f bk.E ^ S.a • (S'.A.map (BK.hf f) * (Y.map (BK.hf f)).map B.D.φ)) * (S.ε f g).map B.D.φ) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = BK.hf g bk.E ^ S.a • ((BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * S.A.map (BK.hf f))) * (S.ε f g).map B.D.φ) := congrArg (fun M => BK.hf g bk.E ^ S.a • (M * (S.ε f g).map B.D.φ)) hYf
      _ = BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * (BK.hf g bk.E ^ S.a • (S.A.map (BK.hf f) * (S.ε f g).map B.D.φ))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * (BK.hf f bk.E ^ S.a • (S.ε f g * S.A.map (BK.hf g)))) := congrArg (fun M => BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * M)) e1
      _ = BK.hf f bk.E ^ S.a • BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * S.ε f g * S.A.map (BK.hf g)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
  rw [Matrix.map_sub, Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, smul_sub, smul_sub]
  · exact congrArg₂ (· - ·) T1 T2
  · exact fun a b => map_sub _ a b
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LiftMatK

variable {l : ℕ} [Fact l.Prime]

theorem pow_mul_mem_integers (K : FinExt l) (a : ↥K.1) : ∃ k : ℕ, (l : ↥K.1) ^ k * a ∈ OL K := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have h1 : IsAlgebraic ℚ_[l] a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ_[l] a := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥K.1).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy
    (PadicInt.irreducible_p (p := l))
  refine ⟨k, ?_⟩
  have h3 := hi.smul ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
  rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow, map_natCast] at h3
  exact h3

theorem lift_one (K : FinExt l) (bk : BK K) (C : Core l) (x : Om l) (hx : x ∈ K.1) (n : ℕ) :
    ∃ (m : ℕ) (s : bk.S), aDp l (bk.ev s) - (l : Per.BdRp l) ^ m * C.o x ∈ Per.FilP l n := by
  obtain ⟨a, ha⟩ := pow_mul_mem_integers K ⟨x, hx⟩
  obtain ⟨k, s, hs, -⟩ := GlobalTheory.BSP.RingHomLiftCongruence.exists_lift l K bk C n ⟨_, ha⟩
  refine ⟨k + a, s, ?_⟩
  have e : ((((⟨_, ha⟩ : ↥(OL K)) : ↥K.1)) : Om l) = (l : Om l) ^ a * x := by
    simp
  rw [e, map_mul, map_pow, map_natCast, ← mul_assoc, ← pow_add] at hs
  exact hs

theorem lift_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (c : Matrix (Fin d) (Fin d) (Om l)), (∀ i j, c i j ∈ K.1) → ∀ n : ℕ, ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * C.o (c i j) ∈ Per.FilP l n := by
  intro l _ K bk C d c hc n
  choose m s hs using fun i j => lift_one K bk C (c i j) (hc i j) n
  let M := Finset.univ.sup (fun p : Fin d × Fin d => m p.1 p.2)
  refine ⟨M, fun i j => (l : bk.S) ^ (M - m i j) * s i j, fun i j => ?_⟩
  have hle : m i j ≤ M := Finset.le_sup (f := fun p : Fin d × Fin d => m p.1 p.2) (Finset.mem_univ (i, j))
  have h := Ideal.mul_mem_left _ ((l : Per.BdRp l) ^ (M - m i j)) (hs i j)
  simp only [map_mul, map_pow, map_natCast]
  convert h using 1
  rw [mul_sub, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

end GlobalTheory.LiftMatK
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 → Function.Injective (toDisc l (s X) ρ) ∧ (∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s) ∧ ∀ ρ' : ℝ≥0, 0 < ρ' → ρ' ≤ ρ → ∀ R : Disc l (s X) ρ →+* Disc l (s X) ρ', IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → Function.Injective R := by
  first | exact @GlobalTheory.BSP.toDisc_injective_of_topBasis | exact GlobalTheory.BSP.toDisc_injective_of_topBasis | (intros; apply GlobalTheory.BSP.toDisc_injective_of_topBasis <;> assumption)
end
