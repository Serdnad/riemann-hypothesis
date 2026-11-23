module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelBaseChangeUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLevelObjPullbackOfCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem dvd_of_mult {p : ℕ} [Fact p.Prime] {m n : ℕ} (hm : m.Coprime p) {s t t' : AfP p}
    (hs : IsIntAf s) (ht' : IsIntAf t') (e : t * t' = 1) (h : (n : AfP p) * t = (m : AfP p) * s) : m ∣ n := by
  have hpos : 0 < m := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hm)
  refine Int.natCast_dvd_natCast.1 (GlobalTheory.IntDvdAdele.dvd_of_eq_mul_int p m hpos hm (n : ℤ) (s * t')
    (GlobalTheory.HeckeApprox.isInt_mul hs ht') ?_)
  rw [Int.cast_natCast, ← _root_.mul_assoc, ← h, _root_.mul_assoc, e, _root_.mul_one]

theorem UpperTheory.Gal.G3.pMultBasic :
    NuInt → MultBasic := by
  intro hNu p _
  refine ⟨?_, ?_, ?_⟩
  · rintro a c c' hc hc' ⟨t, t', ht, ht', e, ha⟩ ⟨s, s', hs, hs', e', ha'⟩
    have h : (c : AfP p) * t = (c' : AfP p) * s := ha.symm.trans ha'
    exact Nat.dvd_antisymm (dvd_of_mult hc ht hs' e' h.symm) (dvd_of_mult hc' hs ht' e h)
  · rintro a a' c c' ⟨t, t', ht, ht', e, ha⟩ ⟨s, s', hs, hs', e', ha'⟩
    refine ⟨t * s, t' * s', GlobalTheory.HeckeApprox.isInt_mul ht hs, GlobalTheory.HeckeApprox.isInt_mul ht' hs', ?_, ?_⟩
    · rw [_root_.mul_mul_mul_comm, e, e', _root_.one_mul]
    · rw [ha, ha', Nat.cast_mul, _root_.mul_mul_mul_comm]
  · intro D G L u hu
    refine ⟨UpperTheory.Gal.G3.mul u, UpperTheory.Gal.G3.mul u⁻¹, hNu p D G L u (UpperTheory.Gal.Int.Geo.integ_of_mem hu),
      hNu p D G L u⁻¹ (UpperTheory.Gal.Int.Geo.integ_of_mem (inv_mem hu)),
      Units.mul_inv ((u : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2), ?_⟩
    rw [Nat.cast_one, _root_.one_mul]
end

section

set_option autoImplicit false

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.HeckeApprox
open UpperTheory.Gal.Int.Geo (Integ)
open scoped TensorProduct

namespace UpperTheory.Gal.G3

variable {p : ℕ} [Fact p.Prime]

private def DvdInt (g : ℤ) (a : AfP p) : Prop := ∃ t : AfP p, IsIntAf t ∧ a = (g : AfP p) * t

private theorem DvdInt.zero (g : ℤ) : DvdInt g (0 : AfP p) :=
  ⟨0, by simpa using isInt_intCast (p := p) 0, by simp⟩

private theorem DvdInt.add {g : ℤ} {a b : AfP p} (ha : DvdInt g a) (hb : DvdInt g b) : DvdInt g (a + b) := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, isInt_add hs ht, by ring⟩

private theorem DvdInt.neg {g : ℤ} {a : AfP p} (ha : DvdInt g a) : DvdInt g (-a) := by
  obtain ⟨s, hs, rfl⟩ := ha
  refine ⟨(-1 : ℤ) * s, isInt_mul (isInt_intCast _) hs, ?_⟩
  push_cast; ring

private theorem dvdInt_form (D : Datum p) (g : ℤ) (hg : ∀ x y, g ∣ D.EF x y) (v w : AfP p ⊗[ℚ] VQ D)
    (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) : DvdInt g (fAf D v w) := by
  have hgen : ∀ z ∈ {z | ∃ (a : AfP p) (x : D.La), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)},
      ∀ w ∈ LaHat D, DvdInt g (fAf D z w) := by
    rintro z ⟨a, x, ha, rfl⟩ w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨a', y, ha', rfl⟩ := hw'
      obtain ⟨c, hc⟩ := hg x y
      refine ⟨(c : AfP p) * (a * a'), isInt_mul (isInt_intCast c) (isInt_mul ha ha'), ?_⟩
      simp only [fAf, LinearMap.BilinForm.baseChange_tmul, hc]
      simp [Algebra.smul_def]
      ring
    | zero => rw [map_zero]; exact DvdInt.zero g
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add (f := _)]; exact h₁.add h₂
    | neg w _ h => rw [map_neg]; exact h.neg
  induction hv using AddSubgroup.closure_induction with
  | mem z hz => exact hgen z hz w hw
  | zero => rw [map_zero, LinearMap.zero_apply]; exact DvdInt.zero g
  | add v₁ v₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact h₁.add h₂
  | neg v _ h => rw [map_neg, LinearMap.neg_apply]; exact h.neg

private theorem exists_form_ne (D : Datum p) : ∃ x y, D.EF x y ≠ 0 := by
  have := D.freeLa
  have := D.finLa
  have hpos : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) Module.finrank_pos
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := ℤ) hpos
  obtain ⟨x, hx⟩ := exists_ne (0 : D.La)
  have h1 : D.EF x ≠ 0 := fun h => hx (D.nondeg (by rw [h, map_zero]))
  obtain ⟨y, hy⟩ := not_forall.1 fun h => h1 (LinearMap.ext h)
  exact ⟨x, y, by simpa using hy⟩

theorem pNuInt : NuInt := by
  intro p _ D G L h hh
  classical
  set I : Ideal ℤ := Ideal.span (Set.range fun q : D.La × D.La => D.EF q.1 q.2) with hI
  set g : ℤ := Submodule.IsPrincipal.generator I with hgdef
  have hspan : I = Ideal.span {g} := (Ideal.span_singleton_generator I).symm
  have hdvd : ∀ x y, g ∣ D.EF x y := fun x y => by
    have : D.EF x y ∈ I := Ideal.subset_span ⟨(x, y), rfl⟩
    rw [hspan] at this
    exact Ideal.mem_span_singleton.1 this
  have hg0 : g ≠ 0 := by
    obtain ⟨x, y, hxy⟩ := exists_form_ne D
    rintro h0
    exact hxy (by simpa [h0] using hdvd x y)
  have key : ∀ z ∈ I, DvdInt g (mul h * (z : AfP p)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨x, y⟩, rfl⟩ := hz
      have e := GlobalTheory.T.harrisTaylor_action_form_eq_similitude_mul p D G L h (inAf D x) (inAf D y)
      have e' : mul h * ((D.EF x y : ℤ) : AfP p) = fAf D (L.actG h (inAf D x)) (L.actG h (inAf D y)) := by
        rw [← form_inAf]; exact e.symm
      simp only [e']
      exact dvdInt_form D g hdvd _ _ (hh _ (inAf_mem D x)) (hh _ (inAf_mem D y))
    | zero => simpa using DvdInt.zero g
    | add a b _ _ ha hb =>
      push_cast
      rw [mul_add]
      exact ha.add hb
    | smul a b _ hb =>
      obtain ⟨t, ht, e⟩ := hb
      refine ⟨(a : AfP p) * t, isInt_mul (isInt_intCast a) ht, ?_⟩
      simp only [smul_eq_mul]
      push_cast
      linear_combination (a : AfP p) * e
  obtain ⟨w, hw, e⟩ := key g (by rw [hspan]; exact Ideal.mem_span_singleton_self g)
  have hu : IsUnit ((g : ℤ) : AfP p) := by
    have : ((g : ℚ)) ≠ 0 := by exact_mod_cast hg0
    have h2 : IsUnit (algebraMap ℚ (AfP p) (g : ℚ)) := (IsUnit.mk0 _ this).map _
    simpa using h2
  have : mul h = w := hu.mul_left_cancel (by rw [mul_comm]; exact e)
  rw [this]
  exact hw

end UpperTheory.Gal.G3

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u


open GlobalTheory.CechPic GlobalTheory.BirigUniq in
theorem UpperTheory.Gal.G3.pPolUniq :
    PolUniq := by
  intro S A A' _ _ _ _ hA hA' ψ hm hfin het hsurj P Q hP hQ h1 h2 h3 h4 hiso
  have hfl : Flat (Over.Hom.left ψ) := inferInstance
  have hqc : QuasiCompact (Over.Hom.left ψ) := inferInstance
  have hcls : ∀ {Y : Scheme} (F : Y ⟶ (G2 A').left),
      pull F (cls P hP - cls Q hQ) = cls (P.pull F) (pull_isLB hP F) - cls (Q.pull F) (pull_isLB hQ F) := by
    intro Y F
    rw [map_sub]
    rfl
  have hzero : ∀ {Y : Scheme} (F : Y ⟶ (G2 A').left), LBIso (P.pull F) (Q.pull F) →
      pull F (cls P hP - cls Q hQ) = 0 := by
    intro Y F h
    rw [hcls, sub_eq_zero]
    exact (cls_eq_iff _ _).mpr h
  set d := cls P hP - cls Q hQ with hd
  have hs1 : pull (Over.Hom.left (lift (1 : A' ⟶ A') (𝟙 A'))) d = 0 := by
    rw [hcls, sub_eq_zero, (cls_eq_zero_iff _).mpr h1, (cls_eq_zero_iff _).mpr h3]
  have hs2 : pull (Over.Hom.left (lift (𝟙 A') (1 : A' ⟶ A'))) d = 0 := by
    rw [hcls, sub_eq_zero, (cls_eq_zero_iff _).mpr h2, (cls_eq_zero_iff _).mpr h4]
  have hsq : pull (Hecke.sq2 ψ) d = 0 := hzero _ hiso
  let E : A' ⊗ A ⟶ A' ⊗ A' := lift (fst A' A) (snd A' A ≫ ψ)
  let W : A ⊗ A' ⟶ A' ⊗ A := lift (snd A A') (fst A A')
  let W' : A' ⊗ A ⟶ A ⊗ A' := lift (snd A' A) (fst A' A)
  have hf : pull (Over.Hom.left (W ≫ E)) d = 0 := by
    refine pic_eq_zero_of_fpqc A A' A hA ψ hfl hsurj hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : A' ⟶ A) (𝟙 A') ≫ W ≫ E = lift (𝟙 A') (1 : A' ⟶ A') := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [E, W, one_comp_monHom]
      rw [this, hs2]
    · rw [← pull_comp_left]
      have : lift (fst A A) (snd A A ≫ ψ) ≫ W ≫ E
          = lift (snd A A) (fst A A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [E, W]
      rw [this, pull_comp_left]
      have h' : pull (Over.Hom.left (lift (fst A A ≫ ψ) (snd A A ≫ ψ))) d = 0 := hsq
      rw [h', map_zero]
  have he : pull (Over.Hom.left E) d = 0 := by
    have : W' ≫ W ≫ E = E := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [E, W, W']
    rw [← this, pull_comp_left, hf, map_zero]
  have hd0 : d = 0 := pic_eq_zero_of_fpqc A' A' A hA' ψ hfl hsurj hqc d hs1 he
  rw [hd, sub_eq_zero] at hd0
  exact (cls_eq_iff hP hQ).mp hd0
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private lemma smooth_pow_hom {S : Scheme.{0}} (A : Over S) (hA : Smooth A.hom) (k : ℕ) :
    Smooth (GlobalTheory.KS.pow A k).hom := by
  have hiso : ∀ {X Y : Over S} (e : X ≅ Y), Smooth Y.hom → Smooth X.hom := by
    intro X Y e h
    rw [← Over.w e.hom]
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).mapIso e).hom)
    infer_instance
  have hprod : ∀ (Y Z : Over S), Smooth Y.hom → Smooth Z.hom → Smooth (Y ⨯ Z).hom := by
    intro Y Z hY hZ
    rw [← Over.w (prod.snd (X := Y) (Y := Z)), ← Over.prodLeftIsoPullback_hom_snd]
    infer_instance
  induction k with
  | zero =>
    exact hiso (((isLimitEquivIsTerminalOfIsEmpty _ _) (productIsProduct _)).uniqueUpToIso
      Over.mkIdTerminal) (by dsimp; infer_instance)
  | succ k ih =>
    exact hiso ((productIsProduct _).conePointUniqueUpToIso
      (extendFanIsLimit _ (productIsProduct fun _ : Fin k => A) (prodIsProd _ _))) (hprod _ _ hA ih)

theorem UpperTheory.Gal.G3.pPowSm :
    GenSm → PowSm := by
  intro hG p _ D R _ _ gb N X k
  obtain ⟨hs, hsep, -, hproj⟩ := hG p D R gb N X
  haveI := hs
  haveI := hsep
  haveI : Smooth X.univ.A.hom := X.univ.ab.smooth
  haveI : Smooth (GlobalTheory.KS.pow X.univ.A k).hom := smooth_pow_hom _ inferInstance k
  haveI : IsProper (GlobalTheory.KS.pow X.univ.A k).hom :=
    GlobalTheory.KS.Leray.isProper_pow_hom _ X.univ.ab.proper k
  refine ⟨inferInstance, inferInstance, fun hD => ?_⟩
  exact GlobalTheory.KS.isProjOver_pow R X.X X.s (hproj hD) X.univ.A X.univ.ab _
    (LB.isLB_pull X.univ.isLB _) X.univ.ample k
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitOne :
    GenSm → WitUniq → WitComp → WitForget → WitOne := by
  intro hS hU hC hF p _ D G L R _ _ gb X N' N hA π Φ hW
  let M : Lv p := ⟨N.1 * N'.1, Nat.le_trans N.2.1 (Nat.le_mul_of_pos_right _ (by have := N'.2.1; omega)),
    Nat.Coprime.mul_left N.2.2 N'.2.2⟩
  have hI : Integ L (1 : G.GAf) := fun v hv => by simpa using hv
  have hMN : AdmK L M.1 N.1 1 := fun u hu => by
    simpa using UpperTheory.Gal.Int.Geo.KN_anti (Dvd.intro _ rfl : N.1 ∣ M.1) hu
  obtain ⟨c, Φc, Wc, cF, cE, cS⟩ := hF p D G L R gb N' M (Dvd.intro_left _ rfl) (X N') (X M)
  obtain ⟨e, Φe, We, eF, eE, eS⟩ := hF p D G L R gb N M (Dvd.intro _ rfl) (X N) (X M)
  have W1 := (hC p D G L R gb M N' N (X M) (X N') (X N) 1 1).2 hI hA c Φc π Φ Wc hW
  rw [_root_.mul_one] at W1
  have hce : c ≫ π = e := (hU p D G L R gb M N (X M) (X N) 1 hI hMN _ _ _ _ W1 We).1
  obtain ⟨s1, s2, s3, -⟩ := hS p D R gb N' (X N')
  obtain ⟨t1, t2, t3, -⟩ := hS p D R gb N (X N)
  have hs : π ≫ (X N).s = (X N').s := hW.1
  have sep : IsSeparated (π ≫ (X N).s) := by rw [hs]; exact s2
  have lft : LocallyOfFiniteType (π ≫ (X N).s) := by rw [hs]; infer_instance
  have πS : IsSeparated π := IsSeparated.of_comp π (X N).s
  have πL : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π (X N).s
  have hE : Etale (c ≫ π) := by rw [hce]; exact eE
  have hFi : IsFinite (c ≫ π) := by rw [hce]; exact eF
  obtain ⟨r1, r2⟩ := GlobalTheory.etale_isFinite_of_comp_etale_surjective _ _ _ c π cE cS hE hFi πS πL
  have hSu : Surjective (c ≫ π) := by rw [hce]; exact eS
  exact ⟨r2, r1, Surjective.of_comp c π⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem kn_le_one {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (N : ℕ) {g : G.GAf}
    (hg : g ∈ L.KN N) : g ∈ L.KN 1 := by
  have key : ∀ {a : G.GAf}, L.CongOne N a → L.CongOne 1 a := by
    intro a ha v hv
    obtain ⟨w, hw, e⟩ := ha v hv
    exact ⟨N • w, nsmul_mem hw N, by rw [e, one_smul]⟩
  exact ⟨key hg.1, key hg.2⟩

theorem UpperTheory.Gal.G3.pWitFree :
    KNBasic → TransComp → TransPull → TransOfMap → TransFree → PtEq → WitCart → WitEx → WitFree := by
  intro hKN hComp hPull hOfMap hFree hPt hCart hEx
  intro p _ D G L R _ _ gb X N' N hle u hu π Φ hW k _ _ x hx
  have hu1 : u ∈ L.KN 1 := kn_le_one L N hu
  have hI1 : Integ L (1 : G.GAf) := UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _)
  have hA1 : AdmK L (↑N') (↑N) (1 : G.GAf) := by
    intro v hv
    simpa using hle hv
  have hA0 : AdmK L (↑N') (↑N') (1 : G.GAf) := (hKN p D G L N').1 1 (one_mem _)
  obtain ⟨π₁, Φ₁, hW1⟩ := hEx p D G L R gb X N' N 1 hI1 hA1
  have hpb1 := hCart p D G L R gb _ _ (X N') (X N) 1 (one_mem _) π₁ Φ₁ hW1
  obtain ⟨_, o, ψ, φ, hψ, _⟩ := hW
  obtain ⟨ox, ⟨mx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ (X N').s) x rfl (X N').univ
  obtain ⟨oo, ⟨m2⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ (X N').s) x rfl o
  obtain ⟨ψ', hψ', _⟩ := hPull p D G L R gb _ _ _ _ x rfl _ _ (X N').univ o ox oo mx m2 ψ u hψ
  have hn1 : Nonempty (GObjMap oo (X N').univ (𝟙 _ ≫ x)) := by
    have h := Unique.gObjMap_comp m2 φ
    have e : x ≫ π = 𝟙 _ ≫ x := by rw [hx, Category.id_comp]
    rwa [e] at h
  obtain ⟨mm⟩ := hn1
  obtain ⟨n⟩ := BaseChange.gObjMap_cancel mm mx
  obtain ⟨θ, _, hθ⟩ := hOfMap p D G L R gb _ _ N' oo ox n
  have hα := hComp p D G L R gb _ _ _ N' N' ox oo ox ψ' θ u 1 hI1 hA0 hψ' hθ
  rw [_root_.one_mul] at hα
  have hpt := (hPt p D G L R gb N' N' N (X N') (X N') (X N) 1 1 u u⁻¹ π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI1 hI1
    hA1 hA1 (inv_mem hu) (by rw [_root_.one_mul, inv_mul_cancel]) k (x ≫ (X N').s) x x rfl rfl
    ox ox mx mx (ψ' ≫ θ) hα).2
  have hpb := IsPullback.paste_horiz mx.cart.1 hpb1
  have hid : ψ' ≫ θ = 𝟙 ox.A := by
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · simpa [Category.assoc] using hpt.symm
    · simp
  rw [hid] at hα
  exact hFree p D G L R gb k (x ≫ (X N').s) N' ox u hu1 hα
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem exists_comp {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} {e : S₁ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g)
    (he : f ≫ g = e) : ∃ m : GObjMap o₁ o₃ e, m.φ = h₁.φ ≫ h₂.φ := by
  subst he
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol
      (GlobalTheory.UPel.HT.MapComp.lbIso_pull_comp h₂.pol h₁.φ₂ rfl)
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem UpperTheory.Gal.G3.pPtOrbit :
    TransComp → TransPull → TransOfMap → TransOrbit → Rigid → PtOrbit := by
  intro hC hP hM hO hRg p _ D G L R _ _ gb N' N X' X π Φ w k _ _ x y hxy
  obtain ⟨e, o, ψ, φ, tψ, rfl⟩ := w
  have hs : y ≫ X'.s = x ≫ X'.s := by rw [← e, ← Category.assoc, ← hxy, Category.assoc]
  obtain ⟨ox, ⟨mx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) x rfl X'.univ
  obtain ⟨oy, ⟨my⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) y hs X'.univ
  obtain ⟨ox', ⟨nx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) x rfl o
  obtain ⟨oy', ⟨ny⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) y hs o
  refine ⟨ox, oy, mx, my, hs, ?_⟩
  obtain ⟨ψx, tx, cx⟩ := hP p D G L R gb X'.X (Sp k) X'.s (x ≫ X'.s) x rfl _ _ X'.univ o ox ox' mx nx ψ 1 tψ
  obtain ⟨ψy, ty, cy⟩ := hP p D G L R gb X'.X (Sp k) X'.s (x ≫ X'.s) y hs _ _ X'.univ o oy oy' my ny ψ 1 tψ
  obtain ⟨A, hA⟩ := exists_comp nx φ (rfl : x ≫ π = x ≫ π)
  obtain ⟨B, hB⟩ := exists_comp ny φ hxy.symm
  obtain ⟨A', hA'⟩ := exists_comp nx φ (Category.id_comp (x ≫ π)).symm
  obtain ⟨c⟩ := BaseChange.gObjMap_cancel (f := 𝟙 (Sp k)) A' B
  obtain ⟨θ', hθ', tθ'⟩ := hM p D G L R gb (Sp k) (x ≫ X'.s) N ox' oy' c
  have i1 : Integ L 1 := UpperTheory.Gal.Int.Geo.integ_of_mem (L.KN 1).one_mem
  have a1 : AdmK L N N 1 := fun v hv => by simpa using hv
  have t₂ := hC p D G L R gb (Sp k) (x ≫ X'.s) N' N N ox ox' oy' ψx θ' 1 1 i1 a1 tx tθ'
  rw [_root_.mul_one] at t₂
  obtain ⟨u, hu, θ, tθ, hθ⟩ := hO p D G L R gb k (x ≫ X'.s) N' N ox oy oy' (ψx ≫ θ') ψy t₂ ty
  refine ⟨u, hu, θ, tθ, ?_⟩
  have hr := hRg p D R gb X.X (Sp k) X.s (x ≫ X'.s) (x ≫ π) (by rw [Category.assoc, e]) N X.univ ox'
  obtain ⟨C, hC'⟩ := exists_comp c B (Category.id_comp (x ≫ π))
  have key : c.φ ≫ ny.φ ≫ φ.φ = nx.φ ≫ φ.φ := by
    have := hr C A
    rw [hC', hB, hA] at this
    exact this
  calc Over.Hom.left θ ≫ my.φ ≫ Over.Hom.left ψ ≫ φ.φ
      = Over.Hom.left θ ≫ (my.φ ≫ Over.Hom.left ψ) ≫ φ.φ := by rw [Category.assoc]
    _ = Over.Hom.left (θ ≫ ψy) ≫ ny.φ ≫ φ.φ := by rw [← cy]; simp
    _ = Over.Hom.left ψx ≫ c.φ ≫ ny.φ ≫ φ.φ := by rw [hθ, Over.comp_left, hθ', Category.assoc]
    _ = Over.Hom.left ψx ≫ nx.φ ≫ φ.φ := by rw [key]
    _ = mx.φ ≫ Over.Hom.left ψ ≫ φ.φ := by rw [← Category.assoc, cx, Category.assoc]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pKNCong :
    KNCong := by
  intro p _ D G L N _ _ u hu h
  have h1 : L.CongOne N u := GlobalTheory.AdelicSim.congOne_of D (L.actG u) N h
  refine ⟨h1, ?_⟩
  intro v hv
  obtain ⟨w₁, hw₁, e₁⟩ := hu.2 v hv
  have hv' : L.actG u⁻¹ v ∈ LaHat D := by
    rw [e₁]
    exact add_mem hv (nsmul_mem hw₁ _)
  obtain ⟨w, hw, e⟩ := h1 _ hv'
  have e' : L.actG u (L.actG u⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  refine ⟨-w, neg_mem hw, ?_⟩
  rw [e'] at e
  rw [smul_neg]
  exact eq_add_neg_of_add_eq e.symm
end
