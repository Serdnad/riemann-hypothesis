module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle282
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle396
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle365
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle418
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVector
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle284
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle271
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle501
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory.AdForm.StabTrans
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Col2.BwLat GlobalTheory.LvT.Built.ValLat Formalism.HermitianLatticesTheory GlobalTheory.Mem.Col2.ValTie

theorem chi_stab {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a i).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (k : Ch → GA B (B.R.N i))
    (hR : I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
      (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k)
    (c : (I.stp u a i).Cl) (s : (I.stp u a i).Stab c) (κ : (K (chOf c)).lev.U)
    (hy : (fun g y x : GA B (B.R.N i) => y = g * y * x) (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
          ((I.stp u a i).gam c.1 s.1)) ((K (chOf c)).y ⟨c, rfl⟩).1 κ.1) :
    ((K (chOf c)).lev.chi κ : ℂ) = B.embLL ((I.stp u a i).chr c.1 s.1 : B.LLˣ) := by
  have h0 := (hR.pt c).of_extTo (I.Q_subset_SQ a) ((LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a))
  have h1 := RatMove.isPtOf_ratAd _ _ B.sp.cm _ _ _ _ s.1.1⁻¹ _ _ h0
  have h2 := lev_part_smul _ _ s.1 ((I.stp u a i).rep c).1.1 (congrArg (fun q => q.1.1) s.2)
  have h3 : ∀ g y x k : GA B (B.R.N i), y = g * y * x → g⁻¹ * (y * k) = y * x * k := fun g y x k h => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← h]
  have h4 : ratAd B.host.F (s.1.1⁻¹) = (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
      ((I.stp u a i).gam c.1 s.1))⁻¹ := by
    rw [ratAd, map_inv, map_inv]
    rfl
  rw [h4, h3 _ _ _ _ hy, ← h2] at h1
  exact hR.chr c κ (1, s.1.2) (map_one (_root_.Formalism.L2.Col.ufGL B.fields.E (B.R.N i))) h1

end GlobalTheory.AdForm.StabTrans

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StabTrans
open Formalism.L2.Theta

theorem finM_mul' {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_mul V g h

theorem rTrans_mul {G : Type} [Monoid G] (a b : G) (F : G → ℂ) : rTrans (a * b) F = rTrans a (rTrans b F) := by
  funext x
  simp only [rTrans, mul_assoc]

theorem rTrans_one {G : Type} [Monoid G] (F : G → ℂ) : rTrans (1 : G) F = F := by
  funext x
  simp only [rTrans, mul_one]

theorem rTrans_list_prod {G α : Type} [Monoid G] (f : α → G) (F : G → ℂ) (h : ∀ i, rTrans (f i) F = F) :
    ∀ L : List α, rTrans (L.map f).prod F = F
  | [] => by simpa using rTrans_one F
  | i :: L => by
    rw [List.map_cons, List.prod_cons, rTrans_mul, rTrans_list_prod f F h L, h i]

end GlobalTheory.AdForm.StabTrans




theorem GlobalTheory.AdForm.trans_stab : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ (e : (I.stp u a j).Cl) (s : (I.stp u a j).Stab e), (I.stp u a j).tr B.fields.emb B.embLL e.1 s.1 ((fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e) = (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hT j hj c hc φ hφ hinv e s
  let eY : (I.chain l u a).Y j ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) j hj :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hR := hA.reads j hj
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hI hP l Z u a j hj (A.bad j) (Ch j) (A.chOf j) (A.K j hj) eY ⟨A.kb j, hR⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF (A.chOf j e))
  have hAd : Ψ ∈ AdFun (A.K j hj (A.chOf j e)).lev (embT (I.rec7 l Z)) := (Submodule.mem_inf.1 hΨ).1
  have hfun : (fun (c : {c // A.chOf j c = A.chOf j e}) (z : Frames (gramC (gramN (I.rec7 l Z) j hj) (embT (I.rec7 l Z)))) =>
      φ c.1 ⟨z.1, z.2⟩) = fun c => Ψ ((A.K j hj (A.chOf j e)).y c) := he.symm
  have rdΨ : ∀ (w : (I.chain l u a).Y j) (g0 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), g0 ∈ GfC _ →
      ∀ x : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F),
      x.1.1 = finM _ (rankN (I.rec7 l Z) j hj) g0 →
      A.rd θ j hj (A.chOf j e) φ w g0 = Ψ x ⟨w.1, w.2⟩ := by
    intro w g0 hg0 x hx
    have hval := (GlobalTheory.AdForm.rdS_val (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X j) (B.R.N j) (rankN (I.rec7 l Z) j hj)
      (gramN (I.rec7 l Z) j hj) rfl (B.T u) (I.rec7 l Z).R.f (A.bad j) (A.K j hj (A.chOf j e)).lev _
      (A.K j hj (A.chOf j e)).y (A.K j hj (A.chOf j e)).y_bij Ψ hAd ⟨w.1, w.2⟩ g0).2.2 x ⟨w.1, w.2⟩ hx (fun τ => by
        have h1 := GlobalTheory.AdForm.ChartVal.infM_fin' θ _ (rankN (I.rec7 l Z) j hj) g0 hg0 τ
        show w.1 τ = infM θ _ _ g0 τ * w.1 τ
        erw [h1, Matrix.one_mul])
    show rdS θ _ (rankN (I.rec7 l Z) j hj) (A.K j hj (A.chOf j e)).lev (A.K j hj (A.chOf j e)).y
      (fun c z => φ c.1 ⟨z.1, z.2⟩) ⟨w.1, w.2⟩ g0 = _
    rw [hfun]
    exact hval
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = Formalism.L2.Col.embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  refine ((GlobalTheory.Mem.Col2.ValTie.stab_inv_iff (E := B.host.E) (F := B.host.F) (sg := sigD (I.rec7 l Z)) (J := gramN (I.rec7 l Z) j hj) (I.stp u a j) B.fields.emb B.embLL e (A.K j hj (A.chOf j e)).lev hemb
    ((A.K j hj (A.chOf j e)).y ⟨e, rfl⟩).1 ((A.K j hj (A.chOf j e)).stabI ⟨e, rfl⟩) (hR.stab e)
    ((A.K j hj (A.chOf j e)).stabI_range ⟨e, rfl⟩)
    (GlobalTheory.AdForm.StabTrans.chi_stab I hI l Z u a j hj (A.chOf j) (A.K j hj) (A.kb j) hR e)
    _ (fun z => ⟨z.1, z.2⟩) (fun _ => rfl)).2 ?_) s
  intro γ hγ κ hy z z' hz

  clear hF hV he hΨ
  obtain ⟨⟨eι, -⟩, -⟩ := id hT
  haveI : Fintype ι := Fintype.ofEquiv _ eι.symm
  classical
  have hJnd : (Finset.univ : Finset ι).toList.Nodup := Finset.nodup_toList _
  have hJall : ∀ i, i ∈ (Finset.univ : Finset ι).toList := fun i => Finset.mem_toList.2 (Finset.mem_univ i)
  obtain ⟨hlev1, hlev2⟩ := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hI hP l Z u a Ch A hA k ι p β Q L hT _ hJnd hJall j hj (A.chOf j e)
  obtain ⟨kA, hkAf, hkAe⟩ := GlobalTheory.Core.Mi.PinModel.exists_finM ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj)
    ⟨κ.1, (((A.K j hj (A.chOf j e)).lev.U_eq κ.1).1 κ.2).1⟩
  have hkAU : kA ∈ A.U j (A.chOf j e) := (hA.U j hj _ kA).2 ⟨hkAf, κ, hkAe.symm⟩
  obtain ⟨g, hg, κ', hκ'off, hdec⟩ := hlev2 kA hkAU
  have hPK : ((Finset.univ : Finset ι).toList.map fun i => (β j i).gl (g i)).prod ∈
      (A.chi j (A.chOf j e)).ker.map (A.U j (A.chOf j e)).subtype := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h, h1⟩ := hlev1 i (g i) (hg i)
    exact ⟨⟨_, h⟩, h1, rfl⟩
  obtain ⟨P0, hP0chi, hP0e⟩ := Subgroup.mem_map.1 hPK
  rw [MonoidHom.mem_ker] at hP0chi
  set P := ((Finset.univ : Finset ι).toList.map fun i => (β j i).gl (g i)).prod with hPdef
  have hP0e' : P0.1 = P := hP0e
  have hκ'U : κ' ∈ A.U j (A.chOf j e) := by
    have : κ' = P0.1⁻¹ * kA := by rw [hdec, hP0e']; group
    rw [this]
    exact mul_mem (inv_mem P0.2) hkAU
  obtain ⟨κ'', hκ''⟩ := ((hA.U j hj _ κ').1 hκ'U).2
  have hchi : ((A.K j hj (A.chOf j e)).lev.chi κ : ℂ) = ((A.K j hj (A.chOf j e)).lev.chi κ'' : ℂ) := by
    rw [← hA.chi j hj _ ⟨kA, hkAU⟩ κ hkAe.symm, ← hA.chi j hj _ ⟨κ', hκ'U⟩ κ'' hκ'']
    have e1 : (⟨kA, hkAU⟩ : A.U j (A.chOf j e)) = P0 * ⟨κ', hκ'U⟩ := Subtype.ext (by
      show kA = P0.1 * κ'
      rw [hP0e', hdec])
    rw [e1, map_mul, hP0chi, one_mul]

  obtain ⟨-, -, hAtF, -, hcm, -, -, hOff, -⟩ := GlobalTheory.FinPl.SetCut.grp_split (I.rec7 l Z) ((I.rec7 l Z).sp.X j) (Finset.univ.image fun i => (p i).v)
  have hPQ : (fun x => ∃ i, x = (p i).v) = (· ∈ (Finset.univ.image fun i => (p i).v)) := by
    funext x
    apply propext
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  have hκ'at : κ' ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∉ (Finset.univ.image fun i => (p i).v)) := by
    have h1 : κ' ∈ GfC _ ⊓ grpOff ((I.rec7 l Z).sp.X j) (fun x => ∃ i, x = (p i).v) :=
      ⟨((hA.U j hj _ κ').1 hκ'U).1, hκ'off⟩
    rw [hOff] at h1
    have hPQn : (fun x => ¬ ∃ i, x = (p i).v) = (· ∉ (Finset.univ.image fun i => (p i).v)) :=
      funext fun x => congrArg Not (congrFun hPQ x)
    rw [hPQn] at h1
    exact h1
  have hcomm : ∀ g' ∈ c.support, g' * κ' = κ' * g' := fun g' hg' => hcm g' (hPQ ▸ hc g' hg') κ' hκ'at
  have hsuppF : ∀ g' ∈ c.support, g' ∈ GfC ((I.rec7 l Z).sp.X j) := fun g' hg' => hAtF (hPQ ▸ hc g' hg')
  have hPf : P ∈ GfC ((I.rec7 l Z).sp.X j) := hP0e' ▸ ((hA.U j hj _ P0.1).1 P0.2).1
  have hhe := hA.h j hj (A.chOf j e) ⟨e, rfl⟩
  have term : ∀ g' ∈ c.support, A.rd θ j hj (A.chOf j e) φ ⟨z.1, z.2⟩ (A.h j (A.chOf j e) ⟨e, rfl⟩ * g') =
      ((A.K j hj (A.chOf j e)).lev.chi κ'' : ℂ) * A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩ (A.h j (A.chOf j e) ⟨e, rfl⟩ * P * g') := by
    intro g' hg'
    obtain ⟨x1, hx1⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
      (A.h j (A.chOf j e) ⟨e, rfl⟩ * g')
    obtain ⟨x2, hx2⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
      (A.h j (A.chOf j e) ⟨e, rfl⟩ * P * g')
    have a1 := rdΨ ⟨z.1, z.2⟩ _ (mul_mem hhe.1 (hsuppF g' hg')) x1 hx1
    have a2 := rdΨ ⟨z'.1, z'.2⟩ _ (mul_mem (mul_mem hhe.1 hPf) (hsuppF g' hg')) x2 hx2
    rw [a1, a2]
    refine hAd γ hγ x2 x1 κ'' ?_ z z' hz
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hx1, hx2, hκ'']
    have hyv := congrArg Units.val hy
    erw [Units.val_mul, Units.val_mul] at hyv
    have hk : kA * g' = P * g' * κ' := by rw [hdec, mul_assoc, ← hcomm g' hg', ← mul_assoc]
    have e2 := congrArg (finM ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj)) hk
    simp only [StabTrans.finM_mul'] at e2 ⊢
    conv_lhs => rw [hhe.2, hyv, ← hhe.2]
    erw [← hkAe]
    simp only [Matrix.mul_assoc] at e2 ⊢
    rw [← e2]
    try rfl
  have hinvP := congrFun (StabTrans.rTrans_list_prod (fun i => (β j i).gl (g i)) (trc c (A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩))
    (fun i => hinv _ _ i (g i) (hg i)) (Finset.univ : Finset ι).toList) (A.h j (A.chOf j e) ⟨e, rfl⟩)
  rw [← hPdef] at hinvP
  show trc c (A.rd θ j hj (A.chOf j e) φ ⟨z.1, z.2⟩) (A.h j (A.chOf j e) ⟨e, rfl⟩) =
    ((A.K j hj (A.chOf j e)).lev.chi κ : ℂ) * trc c (A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩) (A.h j (A.chOf j e) ⟨e, rfl⟩)
  rw [← hinvP, hchi]
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g' hg' => ?_
  rw [term g' hg']
  ring
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLevPrime

section Comp



variable {D : D7}

theorem prV_comm (v : GlobalTheory.FinPl.Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.comm_tmul]
    simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
    rfl
  | add a b ha hb =>
    simp only [map_add (f := _)]
    exact congrArg₂ (· + ·) ha hb

theorem prV_toEAf_congr (v : GlobalTheory.FinPl.Pl D) {y y' : AE D} (h : GlobalTheory.FinPl.compAt D v y = GlobalTheory.FinPl.compAt D v y') :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = Formalism.UG.prV (E := D.host.E) v (toEAf D y') := by
  unfold GlobalTheory.FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  generalize finPart D y' = z' at h ⊢
  refine (prV_comm v z).trans (Eq.trans ?_ (prV_comm v z').symm)
  rw [h]

theorem bc_eq_one_of_off (V : HSp D) {n : ℕ} (hn : V.rank = n) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : P v)
    {g : GA D V} (hg : g ∈ GlobalTheory.FinPl.grpOff V P) {x : GL (Fin n) (EF D)} (hx : x.1 = finM V hn g) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j
  subst hn
  have h := (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V P g).1 hg i j v hv
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  have e : x.1 i j = toEAf D (Formalism.L2.Theta.mt V g i j) := by rw [hx]; rfl
  rw [e, prV_toEAf_congr v h]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero]

end Comp

section Level

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word}

theorem exists_splitPt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k} {β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)}
    {Q : ∀ j, ι → GlobalTheory.LatPair.Pair k (Fin ((I.rec7 l Z).sp.X j).rank)} {L : ∀ j, GlobalTheory.FinPl.Lat ((I.rec7 l Z).sp.X j)}
    (hS : StdT I l Z u p β Q L) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))
    (hv : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) : ∃ i, v = (p i).v := by
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := l.pr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  obtain ⟨w, hw, rfl⟩ := (GlobalTheory.NormPlaces.places_dvd_iff (I.rec7 l Z) (X.piT u) (B.fields.conjO (X.piT u)) (B.T u) rfl
    (l.pr.piT_norm u) hne v).1 hv
  obtain ⟨e, he⟩ := hS.1
  refine ⟨e.symm ⟨w, hw⟩, ?_⟩
  have h := he (e.symm ⟨w, hw⟩)
  rw [e.apply_symm_apply] at h
  exact (GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under _ h).symm



theorem uloc_le_of_std (hOk : I.Ok) (hP : TC.Pins B X) {a a' : I.ι} {Ch Ch' : ℕ → Type} {A : TwDat I l Z u a Ch}
    {A' : TwDat I l Z u a' Ch'} (hA : A.Is) (hA' : A'.Is)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k} {β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)}
    {Q : ∀ j, ι → GlobalTheory.LatPair.Pair k (Fin ((I.rec7 l Z).sp.X j).rank)} {L : ∀ j, GlobalTheory.FinPl.Lat ((I.rec7 l Z).sp.X j)}
    (hS : StdT I l Z u p β Q L) (J : List ι) (hn : J.Nodup) (hall : ∀ i, i ∈ J) (j : ℕ) (hj : j ≤ B.R.m) (b : Ch j) (b' : Ch' j)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ∃ i, v = (p i).v) :
    (A.K j hj b).lev.Uloc v ≤ (A'.K j hj b').lev.Uloc v := by
  intro h hh
  obtain ⟨x, hxU, hxv⟩ : ∃ x ∈ (A.K j hj b).lev.U, Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) x = h := by
    refine ⟨Formalism.UG.P.afsplitU v h 1, ?_, Formalism.UG.P.afsplit_right1 v h 1⟩
    rw [(A.K j hj b).lev.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v _ _ h 1 ((A.K j hj b).lev.Uloc_le v hh) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · rw [hw, Formalism.UG.P.afsplit_right1 v h 1]; exact hh
    · have hxw : Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) w) (Formalism.UG.P.afsplitU v h 1) = 1 := by
        apply Units.ext
        rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw,
          Units.val_one, Units.val_one]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [hxw]; exact one_mem _
  obtain ⟨g, hgC, hg⟩ := GlobalTheory.ChartLevRead.exists_finM_GfC _ (rankN (I.rec7 l Z) j hj) ⟨x, (((A.K j hj b).lev.U_eq x).1 hxU).1⟩
  have hgU : g ∈ A.U j b := (hA.U j hj b g).2 ⟨hgC, ⟨x, hxU⟩, hg.symm⟩
  obtain ⟨g', hg', κ', hκ', hκe⟩ := (GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a Ch A hA k ι p β Q L hS J hn hall j hj b).2 g hgU
  have hst := (GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a' Ch' A' hA' k ι p β Q L hS J hn hall j hj b').1
  have hprod : (J.map fun i => (β j i).gl (g' i)).prod ∈ A'.U j b' := Subgroup.list_prod_mem _ fun y hy => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact (hst i _ (hg' i)).1
  obtain ⟨-, y, hy⟩ := (hA'.U j hj b' _).1 hprod
  obtain ⟨z, hz⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl κ'
  have e : x = y.1 * z.1 := by
    apply Units.ext
    have hg2 : finM _ (rankN (I.rec7 l Z) j hj) g = x.1 := hg
    rw [Units.val_mul, hy, hz, ← hg2, hκe]
    exact GlobalTheory.AdForm.StabMove.finM_mul _ _ _ _
  have hz1 := bc_eq_one_of_off _ (rankN (I.rec7 l Z) j hj) (v := v) hv hκ' hz
  rw [← hxv, e, map_mul, hz1, mul_one]
  exact (((A'.K j hj b').lev.U_eq _).1 y.2).2 v

end Level


end GlobalTheory.PenLevPrime
end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnnFockRev

theorem killed_of_subfamily {P Q V : Type} [AddCommGroup V] [Module ℂ V] (b : Q → V → V) (ι : P → Q) (T : V → Prop)
    (hb : ∀ q f, T f → T (b q f)) (hT : ∀ (c : ℂ) f, T f → T (c • f))
    (hadd : ∀ q f g, T f → T g → b q (f + g) = b q f + b q g)
    (hsmul : ∀ q (c : ℂ) f, b q (c • f) = c • b q f)
    (hdec : ∀ q, ∃ (p p' : P) (c : ℂ), ∀ f, T f → b q f = b (ι p) f + c • b (ι p') f) (N : ℕ) :
    ∀ f, T f → (∀ l : List P, l.length = N → (l.map ι).foldr b f = 0) →
      ∀ l : List Q, l.length = N → l.foldr b f = 0 := by
  have wT : ∀ (l : List Q) f, T f → T (l.foldr b f) := fun l f hf => by
    induction l with
    | nil => exact hf
    | cons q l ih => exact hb _ _ ih
  have wadd : ∀ (l : List Q) f g, T f → T g → l.foldr b (f + g) = l.foldr b f + l.foldr b g := fun l f g hf hg => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hadd _ _ _ (wT l f hf) (wT l g hg)]; rfl
  have wsmul : ∀ (l : List Q) (c : ℂ) f, l.foldr b (c • f) = c • l.foldr b f := fun l c f => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hsmul]; rfl
  have step : ∀ (M : ℕ) (f : V) (p : P), (∀ l : List P, l.length = M + 1 → (l.map ι).foldr b f = 0) →
      ∀ l : List P, l.length = M → (l.map ι).foldr b (b (ι p) f) = 0 := fun M f p h l hl => by
    have := h (l ++ [p]) (by simp [hl])
    rwa [List.map_append, List.foldr_append] at this
  induction N with
  | zero =>
    intro f _ k l hl
    obtain rfl := List.length_eq_zero_iff.1 hl
    exact k [] rfl
  | succ N ih =>
    intro f hf k l hl
    obtain rfl | ⟨l', q, rfl⟩ := l.eq_nil_or_concat'
    · simp at hl
    have hl' : l'.length = N := by simpa using hl
    obtain ⟨p, p', c, h⟩ := hdec q
    rw [List.foldr_append, List.foldr_cons, List.foldr_nil, h f hf,
      wadd _ _ _ (hb _ _ hf) (hT _ _ (hb _ _ hf)), wsmul,
      ih _ (hb _ _ hf) (step _ _ _ k) l' hl', ih _ (hb _ _ hf) (step _ _ _ k) l' hl', smul_zero, add_zero]

theorem dRho_smul_fun {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (c • f) = c • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f := by
  funext w
  simp only [Formalism.IndefR.Datum.dRho, Pi.smul_apply, smul_eq_mul]
  rw [← deriv_const_mul_field]
  congr 1
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem isFockVec_of_sch_mem_fockA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsThetaFunO ψ (dblSp A) B f → sch ψ A B ν 𝓨 f ∈ fockA θ B A.rank l sB → IsFockVec ψ θ (dblSp A) B s' sB f := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl f hth hf
  obtain ⟨N, hN⟩ := GlobalTheory.T.fockPolynomialSchwartz_killed_by_longAnnihilation D θ hθ B A.rank l sB hsB _ hf
  have key : ∀ L : List (D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ),
      IsThetaFunO ψ (dblSp A) B
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) ∧
      sch ψ A B ν 𝓨
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) =
        L.foldr (fun q g => annS B l sB θ q.1 q.2 g) (sch ψ A B ν 𝓨 f) := by
    intro L
    induction L with
    | nil => exact ⟨hth, rfl⟩
    | cons q L ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨isThetaFunO_annih_of_std hψ hθ hν _ _ _ ih1, ?_⟩
      rw [List.foldr_cons, ← ih2]
      exact GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl _ ih1 q.1 q.2
  refine ⟨hth, N, ?_⟩
  refine killed_of_subfamily (P := D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ)
    (Q := D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ)
    (fun p g => annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g)
    (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))) (IsThetaFunO ψ (dblSp A) B)
    (fun q g hg => isThetaFunO_annih_of_std hψ hθ hν _ _ _ hg)
    (fun c g hg => (GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hν g g hg hg c).2.1)
    (fun q g g' hg hg' => ?_) (fun q c g => ?_) (fun q => ?_) N f hth (fun L hL => ?_)
  · simp only [annih]
    rw [GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hg hg', GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hg hg', smul_add]
    abel
  · simp only [annih]
    rw [dRho_smul_fun, dRho_smul_fun, smul_add, smul_comm]
  · obtain ⟨X, X', c, h⟩ := GlobalTheory.T.annihilationOperator_doubledHermitianSpace_decomp D ψ hψ θ hθ A B μ hμ s' sB hs' hsB q.1 q.2
    exact ⟨(q.1, X), (q.1, X'), c, h⟩
  · exact GlobalTheory.T.doubledPairThetaFunction_eq_zero_of_schrodinger_eq_zero D ψ hψ A B ν 𝓨 hν _ (key L).1 ((key L).2.trans (hN L hL))

end GlobalTheory.StdUnnFockRev
end
