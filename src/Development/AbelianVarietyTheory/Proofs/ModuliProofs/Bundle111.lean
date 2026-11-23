module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle105
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle106
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueThetaCharAtPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

@[expose] public section

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoprimeTorsion

open CommutatorPairing

section General

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S)

def chartPullLPow (n : ℕ) : ChartPull (LPow A L n T) (lbPow L n) (snd T A).left where
  idx j := fun _ => j 0
  le j y hy := mem_powChart.2 (Set.mem_iInter.1 hy 0)
  g y j j' hj hj' := by
    refine (gm_linComb L (fun _ : Fin 1 => (snd T A).left) (fun _ => (n : ℤ)) (𝟙 _) y j j' hj hj').trans
      (Eq.trans ?_ (gm_lbPow_g n (snd T A).left y _ _ (mem_powChart.2 (Set.mem_iInter.1 hj 0))
        (mem_powChart.2 (Set.mem_iInter.1 hj' 0))).symm)
    rw [Fin.prod_univ_one, Category.id_comp, zpow_natCast]

theorem nonzeroLocus_chartPullLPow (n : ℕ) (s : (lbPow L n).Sec) :
    nonzeroLocus (chartSec (chartPullLPow A L T n) s) = (snd T A).left ⁻¹ᵁ nonzeroLocus s :=
  nonzeroLocus_chartSec _ s fun _ J hJ => ⟨fun _ => J PUnit.unit, Set.mem_iInter.2 fun _ => mem_powChart.1 hJ⟩

def vanishing (a : ℤ) (E : Set (T ⊗ A).left) : Submodule Γ(T.left, ⊤) (SecM A L a T) where
  carrier := {f | ∀ y ∈ E, y ∉ nonzeroLocus (SecM.toSec A f)}
  add_mem' := by
    intro f f' hf hf' y hy h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    rcases Scheme.basicOpen_add_le _ (f.1 k) (f'.1 k) hk with h | h
    · exact hf y hy (Opens.mem_iSup.2 ⟨k, h⟩)
    · exact hf' y hy (Opens.mem_iSup.2 ⟨k, h⟩)
  zero_mem' := by
    intro y _ h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    exact (Scheme.basicOpen_zero _ _).le hk
  smul_mem' := by
    intro c f hf y hy h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    exact hf y hy (Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_mul _ (liftHom A _ c) (f.1 k)).le hk).2⟩)

variable {A L T}

theorem mem_nonzeroLocus_of_isActOf (hL : L.IsLB) {a : ℤ} {θ : ThetaGrp A L a T} {s s' : LB.Sec (LPow A L a T)}
    (h : IsActOf A L a θ s s') {y : (T ⊗ A).left} (hy : y ∈ nonzeroLocus s') :
    (translT A θ.pt).left y ∈ nonzeroLocus s := by
  obtain ⟨k, hk, hu⟩ := (mem_nonzeroLocus s' y).1 hy
  obtain ⟨i, hi⟩ := exists_chart hL ((translPt A θ.pt).left y)
  obtain ⟨i₀, rfl⟩ : ∃ i₀ : L.ι, k = fun _ => i₀ := ⟨k 0, funext fun b => congrArg k (Subsingleton.elim _ _)⟩
  have hm : y ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] ![i₀, i] := Set.mem_iInter.2 fun b => by
    fin_cases b
    exacts [Set.mem_iInter.1 hk 0, hi]
  have hp := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) ![i₀, i] hm
  have e := (gs_res (𝟙 _) y _ hm _).symm.trans ((congrArg (gs (𝟙 _) y _) (h ![i₀, i])).trans
    ((gs_mul (𝟙 _) y _ hm _ _).trans (congrArg (_ * ·) ((gs_res (𝟙 _) y _ hm _).trans
      (gs_pull (𝟙 _) (translT A θ.pt).left y _ hp _)))))
  have u := isUnit_of_mul_isUnit_right ((congrArg IsUnit e).mp hu)
  rw [Category.id_comp] at u
  exact (mem_nonzeroLocus_iff_pull s (translT A θ.pt).left y (k := fun _ => i) hp).2 u

end General

theorem dense_torsion (hA : AmpleSt) (hK : KerPowSt) (hI : IrredSt) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : PolAV (Sp k)) {p : ℕ} (hp : p.Prime) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ x ^ n = 1}, Set.range x.left) := by
  haveI : IsCommMonObj P.A := P.isAb.comm
  rw [dense_iff_inter_open]
  rintro U hU ⟨y₀, hy₀⟩
  by_contra hne
  obtain ⟨a, -, s, hs, hle, -⟩ := (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).exists_affine_le
    (U := ⟨U, hU⟩) hy₀
  have gen : ∀ N : ℕ, 4 ≤ N → ∀ y : P.A.left, ∃ t : (lbPow P.L N).Sec, y ∈ nonzeroLocus t := fun N hN y => by
    obtain ⟨m, t, ht, -⟩ := veryAmple_lbPow hA k P N hN
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
    exact ⟨t i, hi⟩
  obtain ⟨m, hm, hmp⟩ : ∃ m : ℕ, 4 ≤ m ∧ m.Coprime p :=
    ⟨p * 2 + 1, by have := hp.two_le; omega, by simp⟩
  obtain ⟨t, ht⟩ := gen m hm y₀
  let n := a * p + m
  have hn : 4 ≤ n := le_add_left hm
  have hnp : n.Coprime p := by simpa [n] using hmp
  let σ : (lbPow P.L n).Sec := secMul (secPow s p) t
  have hσ : nonzeroLocus σ = nonzeroLocus s ⊓ nonzeroLocus t := by
    rw [nonzeroLocus_secMul, nonzeroLocus_secPow s hp.one_le]
  let B := baseOver (Sp k)
  let β : ∀ T : Over (Sp k), T ⟶ B := fun T => Over.homMk T.hom (Category.comp_id _)
  let E : Set (B ⊗ P.A).left := ⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ x ^ n = 1},
    Set.range (lift (β _) x).left
  have hsnd : ∀ {T : Over (Sp k)} (x : T ⟶ P.A) (z : T.left), (snd B P.A).left ((lift (β T) x).left z) = x.left z :=
    fun x z => congrArg (fun q => q.left z) (lift_snd (β _) x)
  rcases hI k P n (Or.inr hn) (Nat.cast_ne_zero.2 (by omega)) (vanishing P.A P.L B n E) (fun θ r r' hr h y hy hy' => by
      refine h _ ?_ (mem_nonzeroLocus_of_isActOf P.isLB hr hy')
      obtain ⟨x, ⟨l, hl, hlp, hx⟩, z, rfl⟩ := Set.mem_iUnion₂.1 hy
      have hθ : θ.pt ^ n = 1 := (hK _ P n (by omega) B θ.pt).1 fun q =>
        ⟨⊤, trivial, exists_isGen_pull _ θ.φ θ.isGen _⟩
      refine Set.mem_iUnion₂.2 ⟨(β _ ≫ θ.pt) * x, ⟨n * l, by positivity, Nat.Coprime.mul_left hnp hlp, ?_⟩, z,
        (congrArg (fun q => q.left z) (lift_translT θ.pt (β _) x)).symm⟩
      rw [mul_pow, pow_mul, pow_mul', hx, ← MonObj.comp_pow, hθ, MonObj.comp_one, one_pow, one_pow,
        _root_.mul_one]) with h | h
  · have hmem : SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) σ) ∈ vanishing P.A P.L B n E := fun y hy hy' => by
      obtain ⟨x, hx, z, rfl⟩ := Set.mem_iUnion₂.1 hy
      have h₁ : (snd B P.A).left ((lift (β _) x).left z) ∈ nonzeroLocus σ :=
        (nonzeroLocus_chartPullLPow P.A P.L B n σ).le hy'
      rw [hsnd, hσ] at h₁
      exact hne ⟨_, hle h₁.1, Set.mem_iUnion₂.2 ⟨x, hx, z, rfl⟩⟩
    rw [h, Submodule.mem_bot] at hmem
    have h₂ : (lift (β _) (𝟙 P.A)).left y₀ ∈ nonzeroLocus (chartSec (chartPullLPow P.A P.L B n) σ) :=
      (nonzeroLocus_chartPullLPow P.A P.L B n σ).ge (show (snd B P.A).left _ ∈ nonzeroLocus σ by
        rw [hsnd, hσ]; exact ⟨hs, ht⟩)
    exact (hmem ▸ (vanishing P.A P.L B n Set.univ).zero_mem :
      SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) σ) ∈ vanishing P.A P.L B n Set.univ) _ trivial h₂
  · let z : (𝟙_ (Over (Sp k))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
    obtain ⟨τ, hτ⟩ := gen n hn ((1 : 𝟙_ (Over (Sp k)) ⟶ P.A).left z)
    have hmem : SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) τ) ∈ vanishing P.A P.L B n E := by
      rw [h]; trivial
    refine hmem ((lift (β _) 1).left z) (Set.mem_iUnion₂.2 ⟨1, ⟨1, one_pos, by simp, one_pow _⟩, z, rfl⟩)
      ((nonzeroLocus_chartPullLPow P.A P.L B n τ).ge ?_)
    show (snd B P.A).left _ ∈ nonzeroLocus τ
    rw [hsnd]; exact hτ

end GlobalTheory.CoprimeTorsion
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.lineBundleIso_linComb_symm_biadditive_substitution : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Pb : LB (G2 A).left), Pb.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso Pb (Pb.pull (lift (snd A A) (fst A A)).left) → ∀ (T : Over S) (n m : ℕ) (x : Fin n → (T ⟶ A)) (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (c : Matrix (Fin m) (Fin n) ℤ), W' + W'.transpose = c.transpose * (W + W.transpose) * c → LBIso (LB.LinComb Pb (K := Fin n × Fin n) (fun uv => (lift (x uv.1) (x uv.2)).left) (fun uv => W' uv.1 uv.2)) (LB.LinComb Pb (K := Fin m × Fin m) (fun uv => (lift (∏ i, x i ^ c uv.1 i) (∏ i, x i ^ c uv.2 i)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.BilinCalc.main | exact GlobalTheory.BilinCalc.main | (intros; apply GlobalTheory.BilinCalc.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaGroupKernel_trivial_of_open_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.KTriv (G i) (M i)) → Out.KTriv A L := by
  first | exact @GlobalTheory.CoverGlue.kTriv_of_cover | exact GlobalTheory.CoverGlue.kTriv_of_cover | (intros; apply GlobalTheory.CoverGlue.kTriv_of_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.eq_one_of_biadditive_slice_trivial_eighthPower : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.KTriv G L → ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  first | exact @GlobalTheory.FormBundleKer.eq_one_of_slice_trivial | exact GlobalTheory.FormBundleKer.eq_one_of_slice_trivial | (intros; apply GlobalTheory.FormBundleKer.eq_one_of_slice_trivial <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

private theorem isMonHom_mul_of_isCommMonObj {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  rw [Hom.mul_def]
  infer_instance

theorem exists_oAct_of_map_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (O : Type) [CommRing O] (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (r : O →+* Module.End ℂ (Fin P.g → ℂ)), (∀ a, ∀ z ∈ u.Λ, r a z ∈ u.Λ) → ∃ act : OAct O P.A, ∀ a z, u.ex (r a z) = u.ex z ≫ act.act a := by
  intro hL hL2 hGen hTh O _ P u r hr

  have key : ∀ a, ∃! f : P.A ⟶ P.A, IsMonHom f ∧ ∀ z, u.ex (r a z) = u.ex z ≫ f := fun a =>
    existsUnique_isMonHom_of_map_lattice hL hL2 hGen hTh P P P.L P.L u u (r a) (hr a)
  choose act hact huniq using key
  have eq_of : ∀ a (h : P.A ⟶ P.A), IsMonHom h → (∀ z, u.ex (r a z) = u.ex z ≫ h) → h = act a :=
    fun a h h1 h2 => huniq a h ⟨h1, h2⟩
  have hom : ∀ a, IsMonHom (act a) := fun a => (hact a).1
  refine ⟨⟨act, hom, ?_, ?_, ?_⟩, fun a z => (hact a).2 z⟩
  · refine (eq_of 1 (𝟙 _) inferInstance ?_).symm
    intro z
    simp
  · intro a b
    refine (eq_of (a * b) (act a ≫ act b) inferInstance ?_).symm
    intro z
    rw [mul_comm a b, map_mul, mul_apply_eq_comp, (hact b).2, (hact a).2, Category.assoc]
  · intro a b
    have := hom a
    have := hom b
    refine (eq_of (a + b) (act a * act b) (isMonHom_mul_of_isCommMonObj _ _) ?_).symm
    intro z

    rw [map_add (f := _), LinearMap.add_apply, u.2, (hact a).2, (hact b).2, MonObj.comp_mul]

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open CechPic

theorem siegPre_bundle_mul_left : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (o : Type) [CommRing o] (s : Sp K ⟶ Sp o) (h k : ℕ) (ζ : o) (c : SiegPre h k ζ s) (P : Out.PolAV (Sp K)) (pr : Fin 8 → (P.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ P.A, ∀ u, x ≫ pr u = y u) → ∀ (T : Over (Sp K)) (x x' y : T ⟶ c.A), ∃ t : LB.Gen (LB.LinComb c.P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]), t.IsGen := by
  intro hΘ K _ o _ s h k ζ c P pr hpr huniv T x x' y
  have := hpr 0
  have := hpr 1

  have hL : (c.P.pull (lift (pr 0) (pr 1)).left).IsLB := pull_isLB c.isLB _
  have hθ := hΘ (Sp K) P _ hL

  have hpt : ∀ z : T ⟶ P.A, CechPic.pull z.left (cls _ hL) =
      CechPic.pull (lift (z ≫ pr 0) (z ≫ pr 1)).left (cls c.P c.isLB) := by
    intro z
    rw [cls_pull c.isLB _ hL, ← pull_comp, ← Over.comp_left, comp_lift]

  have hax₁ : ∀ v : T ⟶ c.A, CechPic.pull (lift (1 : T ⟶ c.A) v).left (cls c.P c.isLB) = 0 := by
    intro v
    have e : lift (1 : T ⟶ c.A) v = v ≫ lift (1 : c.A ⟶ c.A) (𝟙 c.A) := by
      rw [comp_lift, comp_one, Category.comp_id]
    rw [e, Over.comp_left, pull_comp, ← cls_pull c.isLB _ (pull_isLB c.isLB _),
      (cls_eq_zero_iff _).2 c.rig₁, map_zero]
  have hax₂ : ∀ u : T ⟶ c.A, CechPic.pull (lift u (1 : T ⟶ c.A)).left (cls c.P c.isLB) = 0 := by
    intro u
    have e : lift u (1 : T ⟶ c.A) = u ≫ lift (𝟙 c.A) (1 : c.A ⟶ c.A) := by
      rw [comp_lift, comp_one, Category.comp_id]
    rw [e, Over.comp_left, pull_comp, ← cls_pull c.isLB _ (pull_isLB c.isLB _),
      (cls_eq_zero_iff _).2 c.rig₂, map_zero]

  obtain ⟨a, ha, -⟩ := huniv T (fun u => if u = 0 then x else 1)
  obtain ⟨b, hb, -⟩ := huniv T (fun u => if u = 0 then x' else 1)
  obtain ⟨d, hd, -⟩ := huniv T (fun u => if u = 1 then y else 1)
  have ha0 : a ≫ pr 0 = x := by simpa using ha 0
  have ha1 : a ≫ pr 1 = 1 := by simpa using ha 1
  have hb0 : b ≫ pr 0 = x' := by simpa using hb 0
  have hb1 : b ≫ pr 1 = 1 := by simpa using hb 1
  have hd0 : d ≫ pr 0 = 1 := by simpa using hd 0
  have hd1 : d ≫ pr 1 = y := by simpa using hd 1

  have key := lam_mul_left hL hθ a b d
  have e1 : x * x' * (1 : T ⟶ c.A) = x * x' := by rw [_root_.mul_one]
  have e3 : (1 : T ⟶ c.A) * 1 = 1 := by rw [_root_.one_mul]
  have e4 : x * (1 : T ⟶ c.A) = x := by rw [_root_.mul_one]
  have e5 : x' * (1 : T ⟶ c.A) = x' := by rw [_root_.mul_one]
  have e6 : (1 : T ⟶ c.A) * y = y := by rw [_root_.one_mul]
  simp only [lam, hpt, mul_comp, ha0, ha1, hb0, hb1, hd0, hd1, one_comp, e1, e3, e4, e5, e6] at key
  simp only [hax₁, hax₂, sub_zero, add_zero] at key
  refine (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).1 ?_
  rw [cls_linComb c.isLB, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, one_smul, neg_smul]
  rw [key]
  abel

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
  {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem push_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩


omit [GrpObj A] [GrpObj A'] in
theorem lift_sq (sq : IsSquare φ φ₂) {T : Over S} {T' : Over S'} (χ : T.left ⟶ T'.left) (x' y' : T' ⟶ A')
    {Z : Over S} (ψ : T.left ⟶ Z.left) (x y : Z ⟶ A) (hx : χ ≫ x'.left ≫ φ = ψ ≫ x.left)
    (hy : χ ≫ y'.left ≫ φ = ψ ≫ y.left) : χ ≫ (lift x' y').left ≫ φ₂ = ψ ≫ (lift x y).left := by
  refine pullback.hom_ext (f := A.hom) (g := A.hom) ?_ ?_
  · show (χ ≫ (lift x' y').left ≫ φ₂) ≫ (fst A A).left = (ψ ≫ (lift x y).left) ≫ (fst A A).left
    rw [Category.assoc, Category.assoc, sq.1, ← Category.assoc (lift x' y').left, ← Over.comp_left, lift_fst, hx,
      Category.assoc, ← Over.comp_left, lift_fst]
  · show (χ ≫ (lift x' y').left ≫ φ₂) ≫ (snd A A).left = (ψ ≫ (lift x y).left) ≫ (snd A A).left
    rw [Category.assoc, Category.assoc, sq.2, ← Category.assoc (lift x' y').left, ← Over.comp_left, lift_snd, hy,
      Category.assoc, ← Over.comp_left, lift_snd]


omit [GrpObj A] [GrpObj A'] in
theorem diag_iso (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (H : LBIso P' (P.pull φ₂)) :
    LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  obtain ⟨u, hu⟩ := H
  have e : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left :=
    (Category.id_comp _).symm.trans (lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (𝟙 A')
      (Z := A) φ (𝟙 A) (𝟙 A) (by simp) (by simp))
  exact LBIso.chartPull (chartPullId _) (chartPullOut P _ _ φ _ fun _ => e)
    (iso_linComb ((isGen_iff u).1 hu) (fun _ : PUnit => (lift (𝟙 A') (𝟙 A')).left) (fun _ => 1))

theorem nondeg_pull (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left}
    {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂))
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine push_injective h T ((hn _ (pushHom h T x) ?_).trans (map_one _).symm)
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

def secPull (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S') ⟶ A' :=
  Over.homMk (h.1.lift (f ≫ x.left) (𝟙 S') (by
    rw [Category.assoc, Over.w x]; exact (Category.comp_id _).trans (Category.id_comp _).symm)) (h.1.lift_snd _ _ _)

theorem secPull_left (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) : (secPull h x).left ≫ φ = f ≫ x.left :=
  h.1.lift_fst _ _ _

theorem push_secPull (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) (T : Over S') :
    pushHom h T (toUnit T ≫ secPull h x) = toUnit (Over.mk (T.hom ≫ f)) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (secPull h x).left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ x.left
  rw [Category.assoc, secPull_left, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem push_secPull' (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) :
    pushHom h _ (secPull h x) = toUnit _ ≫ x := by
  have e := push_secPull h x (𝟙_ (Over S'))
  rwa [toUnit_unit, Category.id_comp] at e

end GlobalTheory.SiegelPull

namespace GlobalTheory

open SiegelPull

theorem siegPre_pullback : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (c : SiegPre h M ζ s), f ≫ s = s' → (∃ c' : SiegPre h M ζ s', SiegPB c' c f) ∧ ∀ c' : SiegPre h M ζ s', SiegPB c' c f → c.Principal → c'.Principal := by
  intro h M o _ ζ S S' s s' f c hs
  refine ⟨?_, ?_⟩
  · obtain ⟨p⟩ := siegPairPB_nonempty c f
    refine ⟨{
      A := p.A
      ab := p.ab
      P := p.P
      isLB := p.isLB
      rig₁ := p.rig₁
      rig₂ := p.rig₂
      symm := p.symm
      lev := fun a => SiegelPull.secPull p.pb (c.lev a)
      lev_add := fun a b => push_injective p.pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', c.lev_add, MonObj.comp_mul])
      lev_tors := fun a => push_injective p.pb _ (by
        rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one])
      geom := fun k _ _ x β z hx hz => ?_ }, p.φ, p.φ₂, p.pb, p.sq, p.iso, fun a => SiegelPull.secPull_left p.pb _⟩
    obtain ⟨g₁, g₂, g₃⟩ := c.geom k (x ≫ f) β z (by rw [Category.assoc, hs, hx]) hz
    refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
    · rw [← (push_injective p.pb (Over.mk x)).eq_iff, push_secPull, map_one]
      rfl
    · obtain ⟨a, ha⟩ := g₂ (pushHom p.pb (Over.mk x) g) (by
        have := congrArg (pushHom p.pb (Over.mk x)) hg
        rw [map_pow, map_one] at this
        exact this)
      exact ⟨a, push_injective p.pb _ ((push_secPull p.pb _ _).trans ha)⟩
    · exact (weilIs_grpPullback_of_comm S S' c.A p.A f p.φ _ _ (pull_isLB c.isLB _) (pull_isLB p.isLB _) p.pb
        (diag_iso p.sq p.iso) (Over.mk x) M _ _ _ _ _
        (congrArg (fun q => q.left) (push_secPull p.pb (c.lev a) (Over.mk x)).symm)
        (congrArg (fun q => q.left) (push_secPull p.pb (c.lev b) (Over.mk x)).symm)).2 (g₃ a b)
  · rintro c' ⟨φ, φ₂, pb, sq, iso, -⟩ ⟨h₁, h₂⟩
    exact ⟨(pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
      (diag_iso sq iso)).2.1 h₁, nondeg_pull pb sq c.isLB c'.isLB iso h₂⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.existsUnique_thetaChar_of_unif : ThetaUnifAV → Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) → ∀ b₀ ∈ B, ∃! cc : (Fin g → ℂ) × (Fin g → ℂ), ∃ c₁ c₂, cc = (c₁, c₂) ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP {b₀} y (fun b z => (e b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z)) :=
  fun hT hLaws _ _ => GlobalTheory.existsUnique_thetaChar_at_point' hT hLaws
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.sabMap_eq_of_level_eq : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ :=
  GlobalTheory.obj_rigid_of_laws
end
