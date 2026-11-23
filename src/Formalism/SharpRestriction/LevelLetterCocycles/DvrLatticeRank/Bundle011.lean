module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle024
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle026
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPfA
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfDict
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPhi
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle009
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.RankLink

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem toLA_range_le (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n)
    (S : Submodule O (LcQ W T π' c)) :
    LinearMap.range (toLA W T π' c S) ≤ LinearMap.range (toLA W T π' c ⊤) := by
  have e : toLA W T π' c S =
      toLA W T π' c ⊤ ∘ₗ TensorProduct.map LinearMap.id (Submodule.inclusion le_top) := by
    apply TensorProduct.ext'
    intro x s
    simp [toLA, TensorProduct.map_tmul]
  rw [e]
  exact LinearMap.range_comp_le_range _ _

theorem lamLA_le (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    (S : Submodule O (LcQ W T π' c)) : LamLA W T π' Eπ h' c S ≤ LamLA W T π' Eπ h' c ⊤ := by
  unfold LamLA
  exact Submodule.comap_mono (toLA_range_le W T π' c S)

theorem invL_le (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    InvL W T Pt π' Eπ h' c S ≤ LamLA W T π' Eπ h' c ⊤ := by
  unfold InvL
  exact le_trans inf_le_left (lamLA_le W T π' Eπ h' c S)

def iota (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    IIrest W T Pt π' Eπ h' c S →ₗ[O] Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c :=
  Submodule.mapQ _ _ (Submodule.inclusion (invL_le W T Pt π' Eπ h' c S)) (fun x hx => by
    simpa [Submodule.mem_comap] using hx)

theorem iota_inj (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    Function.Injective (iota W T Pt π' Eπ h' c S) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.mem_ker] at hy
  unfold iota at hy
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  simpa [Submodule.mem_comap] using hy

theorem rank_link_of_model [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    (hQ : ModelQ W T Pt π' Eπ h' c) (hR : SecondRankCount W T Pt π' Eπ h' c) : SecondPropositionFree W T Pt π' Eπ h' c := by
  intro S
  obtain ⟨hfin, htf⟩ := hQ
  have hinj := iota_inj W T Pt π' Eπ h' c S
  haveI : Module.Finite O (Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c) := hfin
  haveI : IsNoetherian O (Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c) :=
    isNoetherian_of_isNoetherianRing_of_finite O _
  haveI hfinI : Module.Finite O (IIrest W T Pt π' Eπ h' c S) :=
    Module.Finite.of_injective (iota W T Pt π' Eπ h' c S) hinj
  haveI : NoZeroSMulDivisors O (Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c) := by
    refine ⟨fun {a q} h => ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (htf a q ha h)
  haveI : NoZeroSMulDivisors O (IIrest W T Pt π' Eπ h' c S) :=
    Function.Injective.noZeroSMulDivisors _ hinj (map_zero _) (fun a x => map_smul _ a x)
  exact ⟨hfinI, Module.free_of_finite_type_torsion_free', hR S⟩

end Local


theorem rank_link_holds : Formalism.MainNotions.N.Ln34.SecondPropositionOfRank := by
  intro D HW hM hR l _ hl K LL hG π' E hp T h' hh hC hJ c
  haveI := Formalism.MainNotions.N.Ln34.GenPf.isDVR (D.loc l) LL
  exact rank_link_of_model _ T _ π' _ h' c (hM l hl K LL hG π' E hp h' hh T hC hJ c)
    (hR l hl K LL hG π' E hp T h' hh hC hJ c)

end Formalism.MainNotions.N.Ln34.RankLink

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section NinLamPfLocal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem ninLamPf_local (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Eπ : LetA O n) (h' : ℕ)
    (w : (LetA O n)ˣ) (hs1 : W.s = 1) (hw : W.q = (w : LetA O n) * Eπ)
    (h5 : ∀ i, ∀ y ∈ W.Nl T i, W.Q ^ h' • y ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1))) :
    NinLam W T Eπ h' := by
  intro c y hy
  unfold NcS at hy
  rw [Submodule.mem_inf, Submodule.mem_inf] at hy
  obtain ⟨⟨hyN, hyD⟩, hyL⟩ := hy
  rw [Submodule.restrictScalars_mem] at hyN
  unfold LamPS
  rw [Submodule.mem_inf, Submodule.mem_inf]
  refine ⟨⟨?_, hyD⟩, hyL⟩
  rw [Submodule.restrictScalars_mem, Submodule.mem_comap]
  unfold letS at hyL
  rw [LinearMap.mem_ker] at hyL
  simp only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hyL
  have hNl : y ∈ W.Nl T c := by
    unfold LocWach.Nl
    refine Submodule.mem_map.2 ⟨y, hyN, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, hyL]
  have h5' := h5 c y hNl
  have hQ : W.Q = W.q := by simp [LocWach.Q, hs1]
  have hE : Eπ ^ h' = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) ^ h' * W.Q ^ h' := by
    rw [hQ, hw, mul_pow, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  unfold Formalism.MainNotions.DeltaInvariantLattices.smulA
  rw [LinearMap.smul_apply, LinearMap.id_apply, hE, mul_smul]
  exact Submodule.smul_mem _ _ h5'

end NinLamPfLocal

theorem ninlam_pf : NinLamStep := by
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hp9 T h' hcrys hjumps
  have hT1 := hA.1 l K 1 LL hG
  have hP5 := hT1.2.2.2.2.1
  obtain ⟨w, hw⟩ := hp9.2.2.2.2.1
  have hJ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet ((HW l).W K 1 LL hG) T (fun _ => h') (fun _ => h') := by
    intro τ i _
    exact hjumps τ
  have h5 := (hP5 T (fun _ => h') (fun _ => h') hcrys hJ).2.1
  exact ninLamPf_local _ T _ h' w ((HW l).W_s K 1 LL hG) hw h5

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.CrystallineExponents

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem exists_aut_prim (K : FinExt l) {z z' : Om l} (hz : IsPrimitiveRoot z l)
    (hz' : IsPrimitiveRoot z' l) : ∃ g : Om l ≃ₐ[↥(K0 K)] Om l, g z = z' := by
  have hl : l.Prime := Fact.out
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  haveI : IsAlgClosure ↥(K0 K) (Om l) := ⟨inferInstance, inferInstance⟩
  have hint : IsIntegral ↥(K0 K) z := Algebra.IsIntegral.isIntegral z
  have hle : K0 K ≤ Ks K 1 := le_sup_left
  have hdeg := CyclotomicLifting.cyclotomic_degree_max_unramified K
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle] at hdeg
  have hsub : IntermediateField.extendScalars hle ≤ IntermediateField.adjoin ↥(K0 K) {z} := by
    have h : Ks K 1 ≤ (IntermediateField.adjoin ↥(K0 K) {z}).restrictScalars ℚ_[l] := by
      refine sup_le (fun x hx => ?_) (IntermediateField.adjoin_le_iff.2 fun x hx => ?_)
      · exact (IntermediateField.adjoin ↥(K0 K) {z}).algebraMap_mem ⟨x, hx⟩
      · have hx1 : x ^ l = 1 := by simpa using hx
        obtain ⟨b, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hx1
        exact pow_mem (IntermediateField.mem_adjoin_simple_self ↥(K0 K) z) b
    intro x hx
    exact h hx
  haveI := IntermediateField.adjoin.finiteDimensional hint
  have hd : l - 1 ≤ (minpoly ↥(K0 K) z).natDegree := by
    rw [← IntermediateField.adjoin.finrank hint, ← hdeg]
    exact IntermediateField.finrank_le_of_le_right hsub
  have hroot : ∀ {w : Om l}, IsPrimitiveRoot w l →
      Polynomial.aeval w (Polynomial.cyclotomic l ↥(K0 K)) = 0 := fun {w} hw => by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact hw.isRoot_cyclotomic hl.pos
  have hdvd : minpoly ↥(K0 K) z ∣ Polynomial.cyclotomic l ↥(K0 K) := minpoly.dvd _ _ (hroot hz)
  have heq : Polynomial.cyclotomic l ↥(K0 K) = minpoly ↥(K0 K) z :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (Polynomial.cyclotomic.monic _ _) hdvd
      (by rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hl]; exact hd)
  have h0 : Polynomial.aeval z' (minpoly ↥(K0 K) z) = 0 := heq ▸ hroot hz'
  exact minpoly.exists_algEquiv_of_root' hint.isAlgebraic h0

theorem exists_pt (D : D7) (HW : HWOf D.loc) {K LL : FinExt l} (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ l) :
    ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ := by
  have : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ_[l]) (L := ↥(K0 K))
    (M := Om l) (E := Om l) ((LL.1.val).comp (((HW l).W K 1 LL hG).emb c))
  have hσx : ∀ x : ↥(K0 K),
      σ (x : Om l) = ((((HW l).W K 1 LL hG).emb c x : ↥LL.1) : Om l) := fun x => by
    have := congrArg (fun f => f x) hσ
    simpa [AlgHom.domRestrict] using this
  have hζ₁ := Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hζO : IsPrimitiveRoot ((ζ : ↥LL.1) : Om l) l :=
    hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hσζ₁ : IsPrimitiveRoot (σ ((D.loc l).ζQ 1)) l := hζ₁.map_of_injective hσinj
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨b, -, hb⟩ := hσζ₁.eq_pow_of_pow_eq_one hζO.pow_eq_one
  have hβ : IsPrimitiveRoot ((D.loc l).ζQ 1 ^ b) l := by
    apply IsPrimitiveRoot.of_map_of_injective (f := σ) _ hσinj
    rw [map_pow, hb]
    exact hζO
  obtain ⟨g, hg⟩ := exists_aut_prim K hζ₁ hβ
  let g' : Om l →ₐ[ℚ_[l]] Om l := (g.toAlgHom).restrictScalars ℚ_[l]
  have hmem : ∀ y, ((σ.comp g').comp (Ks K 1).val) y ∈ LL.1 := hG.2.2.2 _
  let τs : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 :=
    ((σ.comp g').comp (Ks K 1).val).codRestrict LL.1.toSubalgebra hmem
  refine ⟨τs.comp (IntermediateField.inclusion hG.2.2.1), τs,
    ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
  · apply Subtype.ext
    show σ (g (y : Om l)) = _
    have hgx : g (x : Om l) = x := g.commutes x
    rw [hxy, hgx, hσx]
  · apply Subtype.ext
    show σ (g (y : Om l)) = _
    rw [hy, hg, map_pow, hb]
  · show τs _ = τs y
    congr 1
    exact Subtype.ext hxy.symm

end Formalism.MainNotions.N.Ln34.CrystallineExponents

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}

theorem framepf_αβ_core (Bs : FramepfBas W T) (hT : IsCrys PD T.ρ) (π' Eπ : LetA O n) (h' M : ℕ)
    (c : ZMod n) (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hEΔ : Eπ ∈ W.AΔ)
    (eb : Fin Bs.r → LcQ W T π' c) (P R S : Fin Bs.r → Fin Bs.r → LetA O n) (hS : ∀ m k, S m k ∈ W.AΔ)
    (lam : O) (hRP : ∀ m k, ∑ j, R m j * P j k =
      (if m = k then algebraMap O (LetA O n) lam * letE c else 0) + π' ^ M * Eπ ^ (4 * h') * S m k)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c)
    (hΨ : ∀ e j, Ψ (e ⊗ₜ eb j) = e • ∑ m, R m j • W.φD T (Bs.b m))
    (hΦ : ∀ a : Fin Bs.r → LetA O n, Φ (∑ k, a k • W.φD T (Bs.b k)) =
      ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * P j k) ⊗ₜ eb j)
    (y : W.DD T) (hy : y ∈ LamPS W T Eπ h' c) : Ψ (Φ y) - lam • y ∈ JP W T π' Eπ h' M c := by
  obtain ⟨h1, hΔ, hl⟩ := (mem_LamPS W T Eπ h' c y).1 hy
  obtain ⟨a, haΔ, hac, ha⟩ := framepf_phi_coordΔ Bs hT c (framepf_φspan_le (c - 1) h1)
    (fun δ hδ => by rw [gradNPf_γD_smul, map_pow, hEΔ δ hδ, hΔ δ hδ])
    (by rw [smul_comm, hl])
  refine ⟨∑ m, (∑ k, a k * S m k) • W.φD T (Bs.b m), framepf_mem_Pc Bs c _
    (fun m => Subalgebra.sum_mem _ fun k _ => W.AΔ.mul_mem (haΔ k) (hS m k)) (fun m => ?_), ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hac]
  show (π' ^ M * Eπ ^ (3 * h')) • (∑ m, (∑ k, a k * S m k) • W.φD T (Bs.b m)) = _
  rw [← sub_eq_zero]
  apply gradNPf_tf W T (Eπ ^ h') (by rw [map_pow]; exact huE.pow _)
  have h2 : Eπ ^ h' • Ψ (Φ y) = ∑ m, (∑ j, (∑ k, a k * P j k) * R m j) • W.φD T (Bs.b m) := by

    rw [← algebraMap_smul W.EE, ← map_smul, ← map_smul, algebraMap_smul, ha, hΦ, map_sum]
    simp only [hΨ, algebraMap_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_smul.symm
  have h3 : ∀ m, ∑ j, (∑ k, a k * P j k) * R m j =
      algebraMap O (LetA O n) lam * a m + π' ^ M * Eπ ^ (4 * h') * ∑ k, a k * S m k := by
    intro m
    have : ∑ j, (∑ k, a k * P j k) * R m j = ∑ k, a k * ∑ j, R m j * P j k := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    simp only [hRP, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · rw [mul_left_comm, mul_comm (a m), hac]
    · exact Finset.sum_congr rfl fun k _ => by ring
  have h4 : Eπ ^ h' • (lam • y) = ∑ m, (algebraMap O (LetA O n) lam * a m) • W.φD T (Bs.b m) := by
    rw [smul_comm, ha, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [mul_smul, algebraMap_smul]
  rw [smul_sub, smul_sub, h2, h4, smul_smul, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [h3, smul_smul, ← sub_smul, ← sub_smul]
  convert zero_smul (LetA O n) (W.φD T (Bs.b m)) using 2
  ring

end Local

end Formalism.MainNotions.N.Ln34

end
end
