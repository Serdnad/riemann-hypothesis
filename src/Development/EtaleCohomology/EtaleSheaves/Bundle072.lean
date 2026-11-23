module

public import Development.EtaleCohomology.EtaleSheaves.Bundle064
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.EtaleSheaves.Bundle065
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.WithTerminal.Lemmas
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.MulPf

def Gen : Prop := ∀ (q : ℕ), ∃ μ : ∀ (j k l : ℤ), j + k = l → ∀ (X : Scheme.{0}), Sec (tw q k) X → (Sec (tw q j) X →+ Sec (tw q l) X),
  (∀ (j k l : ℤ) (h : j + k = l) {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Sec (tw q k) X) (x : Sec (tw q j) X),
      Sec.res f (μ j k l h X y x) = μ j k l h Y (Sec.res f y) (Sec.res f x)) ∧
  (∀ (j k l : ℤ) (h : j + k = l) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)), μ j k l h X (twGen k ζ) (twGen j ζ) = twGen l ζ)

def LocGen : Prop := ∀ (q : ℕ) (j : ℤ) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (x : Sec (tw q j) X),
  ∃ S ∈ Scheme.etaleTopology X, ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X), S f →
    ∃ c : ℤ, Sec.res f x = c • twGen j (ζ.map f.appTop.hom)

theorem sep {q : ℕ} {j : ℤ} {X : Scheme.{0}} (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X) (s t : Sec (tw q j) X)
    (h : ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X), S f → Sec.res f s = Sec.res f t) : s = t :=
  Sheaf.isSeparated (tw q j) X S hS s t (fun _ f hf => h f hf)

theorem twGen_pow {q : ℕ} (m : ℤ) {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen m ξ = (ULift.up.{1} ((a ^ m : (ZMod q)ˣ) : ZMod q)) • twGen m ζ := by
  unfold twGen ofRings.sec
  have hmem : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single ζ (ULift.up ((a ^ m : (ZMod q)ˣ) : ZMod q)) ∈ twRel q m Γ(U, ⊤) :=
    Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have key : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q m).obj Γ(U, ⊤)) =
      (ULift.up.{1} ((a ^ m : (ZMod q)ˣ) : ZMod q)) • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q m).obj Γ(U, ⊤)) := by
    refine ((Submodule.Quotient.eq (twRel q m Γ(U, ⊤))).2 hmem).trans ?_
    rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact (congrArg (fun v => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q m)).app (op U)).hom v) key).trans (map_smul _ _ _)

theorem locPres {q : ℕ} {j : ℤ} {X : Scheme.{0}} (x : Sec (tw q j) X) :
    ∃ S ∈ Scheme.etaleTopology X, ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X), S f →
      ∃ v : (twF q j).obj Γ(Y, ⊤), Sec.res f x = ofRings.sec (twF q j) Y v := by
  refine ⟨_, Presheaf.imageSieve_mem (J := Scheme.etaleTopology) (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q j))
    (U := op X) x, fun Y f hf => ?_⟩
  obtain ⟨t, ht⟩ := hf
  exact ⟨t, ht.symm⟩

def RootPow : Prop := ∀ (q : ℕ) (Y : Scheme.{0}) (ζ : Prim q Γ(Y, ⊤)) (s : Finset (Prim q Γ(Y, ⊤))),
  ∃ S ∈ Scheme.etaleTopology Y, ∀ ⦃Z : Scheme.{0}⦄ (g : Z ⟶ Y), S g → ∀ ξ ∈ s,
    ∃ a : (ZMod q)ˣ, (ξ.map g.appTop.hom).1 = (ζ.map g.appTop.hom).1 ^ (a : ZMod q).val

theorem secRes {q : ℕ} {j : ℤ} {V U : Scheme.{0}} (g : V ⟶ U) (v : (twF q j).obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec (twF q j) U v) = ofRings.sec (twF q j) V (((twF q j).map g.appTop).hom v) := by
  unfold ofRings.sec
  have h := congrArg (fun φ => φ.hom v) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q j)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  exact h.symm

theorem sec_single {q : ℕ} {j : ℤ} {U : Scheme.{0}} (ξ : Prim q Γ(U, ⊤)) (c : ULift.{1} (ZMod q)) :
    ofRings.sec (twF q j) U (Submodule.Quotient.mk (Finsupp.single ξ c) : (twF q j).obj Γ(U, ⊤)) = c • twGen j ξ := by
  unfold twGen ofRings.sec
  have key : (Submodule.Quotient.mk (Finsupp.single ξ c) : (twF q j).obj Γ(U, ⊤)) =
      c • (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q j).obj Γ(U, ⊤)) := by
    rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact (congrArg (fun v => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q j)).app (op U)).hom v) key).trans (map_smul _ _ _)

theorem ulift_smul_eq {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (c : ULift.{1} (ZMod q)) (v : M) :
    c • v = ((c.down.cast : ℤ)) • v := by
  have hc : c = (((c.down.cast : ℤ)) : ULift.{1} (ZMod q)) := ULift.ext (by
    show c.down = ((c.down.cast : ℤ) : ULift.{1} (ZMod q)).down
    exact (ZMod.intCast_zmod_cast c.down).symm)
  conv_lhs => rw [hc]
  exact Int.cast_smul_eq_zsmul _ _ _

theorem sec_sum {q : ℕ} {j : ℤ} {U : Scheme.{0}} {ι : Type} (s : Finset ι) (g : ι → (twF q j).obj Γ(U, ⊤)) :
    ofRings.sec (twF q j) U (∑ i ∈ s, g i) = ∑ i ∈ s, ofRings.sec (twF q j) U (g i) := by
  unfold ofRings.sec
  exact map_sum _ _ _

theorem LocGen_of (hR : RootPow) : LocGen := by
  intro q j X ζ x
  obtain ⟨S, hS, hv⟩ := locPres x
  have hv' : ∀ ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X), S f → ∃ w : Prim q Γ(Y, ⊤) →₀ ULift.{1} (ZMod q),
      Sec.res f x = ofRings.sec (twF q j) Y (Submodule.Quotient.mk w : (twF q j).obj Γ(Y, ⊤)) := by
    intro Y f hf
    obtain ⟨v, hv⟩ := hv f hf
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact ⟨w, hv⟩
  choose w hw using hv'
  have hT := fun ⦃Y : Scheme.{0}⦄ (f : Y ⟶ X) (hf : S f) => hR q Y (ζ.map f.appTop.hom) (w f hf).support
  choose T hTmem hTprop using hT
  refine ⟨Sieve.bind S.arrows T, Scheme.etaleTopology.bind_covering hS hTmem, ?_⟩
  rintro Z _ ⟨Y, h, f, hf, hh, rfl⟩
  have hres : Sec.res (h ≫ f) x = Sec.res h (Sec.res f x) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [hres, hw f hf]
  erw [secRes]
  set G := twGen j (ζ.map (h ≫ f).appTop.hom)
  have hmk : (((twF q j).map h.appTop).hom (Submodule.Quotient.mk (w f hf) : (twF q j).obj Γ(Y, ⊤))) =
      ∑ ξ ∈ (w f hf).support, (Submodule.Quotient.mk (Finsupp.single (ξ.map h.appTop.hom) (w f hf ξ)) : (twF q j).obj Γ(Z, ⊤)) := by
    change (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map h.appTop.hom) (w f hf)) : (twF q j).obj Γ(Z, ⊤)) = _

    rw [Finsupp.mapDomain, Finsupp.sum, ← Submodule.mkQ_apply, map_sum]
    rfl
  rw [hmk]
  erw [sec_sum]
  have key : ∃ c : ULift.{1} (ZMod q), ∑ ξ ∈ (w f hf).support, ofRings.sec (twF q j) Z
      (Submodule.Quotient.mk (Finsupp.single (ξ.map h.appTop.hom) (w f hf ξ)) : (twF q j).obj Γ(Z, ⊤)) = c • G := by
    refine Finset.sum_induction _ (fun v => ∃ c : ULift.{1} (ZMod q), v = c • G) ?_ ⟨0, by simp⟩ ?_
    · rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
      exact ⟨c + d, (add_smul c d G).symm⟩
    · intro ξ hξ
      obtain ⟨a, ha⟩ := hTprop f hf h hh ξ hξ
      rw [sec_single, twGen_pow j _ _ a ha, LateralTheory.E.TwistTrivial.prim_map_comp, smul_smul]
      exact ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := key
  exact ⟨_, hc.trans (ulift_smul_eq c G)⟩

theorem Mul_of (hG : Gen) (hL : LocGen) : LateralTheory.E.TwistTrivial.Mul := by
  intro q
  obtain ⟨μ, hnat, hgen⟩ := hG q
  refine ⟨μ, hnat, ?_⟩
  intro j k l k' h h' X ζ x
  obtain ⟨S, hS, hx⟩ := hL q j X ζ x
  refine sep S hS _ _ (fun Y f hf => ?_)
  obtain ⟨c, hc⟩ := hx f hf
  rw [hnat, hnat, LateralTheory.E.TwistTrivial.genRes, LateralTheory.E.TwistTrivial.genRes, hc, map_zsmul, hgen, map_zsmul, hgen]

end LateralTheory.E.MulPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof
  LateralTheory.E.ChartsGeom_vpaPf

namespace LateralTheory.E.ChartOverlap₂

set_option linter.unusedSectionVars false

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem restr_iff (B : Subalgebra A K) (t : K) (S : Subalgebra A K) {R W : Type} [CommRing R] [CommRing W]
    (eR : R ≃+* S) (eW : W ≃+* AdjoinInv B t) (res : R →+* W) (hc : ∀ r, ((eW (res r) : AdjoinInv B t) : K) = (eR r : K))
    (P : PrimeSpectrum W) (x : PrimeSpectrum S) :
    Restr B t (PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* W) P) S x ↔
      PrimeSpectrum.comap (eR : R →+* S) x = PrimeSpectrum.comap res P := by
  have key : ∀ s : S, (∃ d ∈ (PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* W) P).asIdeal, (d : K) = (s : K)) ↔
      res (eR.symm s) ∈ P.asIdeal := by
    intro s
    have hd : eW (res (eR.symm s)) = ⟨(s : K), by simpa [hc] using (eW (res (eR.symm s))).2⟩ := by
      apply Subtype.ext; simp [hc]
    constructor
    · rintro ⟨d, hd1, hd2⟩
      have : d = eW (res (eR.symm s)) := by rw [hd]; exact Subtype.ext hd2
      subst this
      simpa using hd1
    · intro h
      refine ⟨eW (res (eR.symm s)), ?_, by simp [hc]⟩
      simpa using h
  unfold Restr
  simp_rw [key]
  constructor
  · intro h
    ext r
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe]
    have := h (eR r)
    simpa using this
  · intro h s
    have := congrArg (fun q : PrimeSpectrum R => eR.symm s ∈ q.asIdeal) h
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply] at this
    exact Iff.of_eq this

theorem chartMap_base {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K)
    (hi : Function.Injective φ) (B : Subalgebra A K) (hr : φ.range = B.toSubring) (x : PrimeSpectrum B) :
    (chartMap hU φ hi B hr).base x =
      hU.fromSpec.base (PrimeSpectrum.comap (chartEquiv φ hi B hr : Γ(Z, U) →+* B) x) := rfl

theorem fromSpec_res {Z : Scheme.{0}} {U W : Z.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U)
    (P : PrimeSpectrum Γ(Z, W)) :
    hU.fromSpec.base (PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op).hom P) = hW.fromSpec.base P := by
  rw [← hU.map_fromSpec hW (homOfLE h).op]; rfl

theorem Overlap_of : LateralTheory.E.ChartsGeom_vpaPf.Overlap := by
  intro A _ _ K _ _ Z p B C t _ U V φU φV φW hU hV hW hUV iU iV iW rU rV rW cU cV x y
  set eU := chartEquiv φU iU B rU
  set eV := chartEquiv φV iV C rV
  set eW := chartEquiv φW iW (AdjoinInv B t) rW
  have hcU : ∀ r, ((eW ((Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom r) : AdjoinInv B t) : K) =
      (eU r : K) := fun r => cU r
  have hcV : ∀ r, ((eW ((Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom r) : AdjoinInv B t) : K) =
      (eV r : K) := fun r => cV r
  rw [chartMap_base, chartMap_base]
  constructor
  · intro h
    have hzU : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ (U : Set Z) := by
      rw [← hU.range_fromSpec]; exact ⟨_, rfl⟩
    have hzV : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ (V : Set Z) := by
      rw [h, ← hV.range_fromSpec]; exact ⟨_, rfl⟩
    have hz : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ Set.range hW.fromSpec.base := by
      rw [hW.range_fromSpec]; exact ⟨hzU, hzV⟩
    obtain ⟨P, hP⟩ := hz
    refine ⟨PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* Γ(Z, U ⊓ V)) P,
      (restr_iff B t B eU eW _ hcU P x).2 ?_, (restr_iff B t C eV eW _ hcV P y).2 ?_⟩
    · apply hU.fromSpec.isOpenEmbedding.injective
      exact ((fromSpec_res hU hW inf_le_left P).trans hP).symm
    · apply hV.fromSpec.isOpenEmbedding.injective
      exact (h.symm.trans hP.symm).trans (fromSpec_res hV hW inf_le_right P).symm
  · rintro ⟨Q, hx, hy⟩
    have hQ : Q = PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* Γ(Z, U ⊓ V))
        (PrimeSpectrum.comap (eW : Γ(Z, U ⊓ V) →+* AdjoinInv B t) Q) := by
      ext a; simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply]
    rw [hQ] at hx hy
    have hx1 := (restr_iff B t B eU eW _ hcU _ x).1 hx
    have hy1 := (restr_iff B t C eV eW _ hcV _ y).1 hy
    exact (congrArg hU.fromSpec.base hx1).trans ((fromSpec_res hU hW inf_le_left _).trans
      ((fromSpec_res hV hW inf_le_right _).symm.trans (congrArg hV.fromSpec.base hy1).symm))

end LateralTheory.E.ChartOverlap₂
end
end

section

noncomputable section
open Polynomial LateralTheory.E.PartDiagCut

namespace LateralTheory.E.LiftPf

theorem orthF {A : Type} [CommRing A] (P : PartDiagCut.Part A) {n : ℕ} (ε : Fin n → A)
    (hfo : ∀ l m, l ≠ m → ε l * ε m = 0) {e e' : A} (he : e ∈ P.1) (he' : e' ∈ P.1) {l m : Fin n}
    (hne : (e, l) ≠ (e', m)) : e * ε l * (e' * ε m) = 0 := by
  by_cases hee : e = e'
  · subst hee
    have hlm : l ≠ m := fun h => hne (by rw [h])
    calc e * ε l * (e * ε m) = e * e * (ε l * ε m) := by ring
      _ = 0 := by rw [hfo l m hlm, mul_zero]
  · calc e * ε l * (e' * ε m) = (e * e') * (ε l * ε m) := by ring
      _ = 0 := by rw [P.orth e he e' he' hee, zero_mul]

theorem refine_exists {A : Type} [CommRing A] (P : PartDiagCut.Part A) {n : ℕ} (ε : Fin n → A)
    (hfi : ∀ l, IsIdempotentElem (ε l)) (hfo : ∀ l m, l ≠ m → ε l * ε m = 0)
    (hfs : ∑ l, ε l = 1) : ∃ Q : PartDiagCut.Part A, P ≤ Q ∧ ∀ g ∈ Q.1, ∃ l, g * ε l = g := by
  classical
  let F : A × Fin n → A := fun x => x.1 * ε x.2
  let T := (P.1 ×ˢ (Finset.univ : Finset (Fin n))).filter (fun x => F x ≠ 0)
  have memT : ∀ x ∈ T, x.1 ∈ P.1 ∧ F x ≠ 0 := by
    intro x hx
    simp only [T, Finset.mem_filter, Finset.mem_product] at hx
    exact ⟨hx.1.1, hx.2⟩
  have idF : ∀ x ∈ T, IsIdempotentElem (F x) := fun x hx => (P.idem x.1 (memT x hx).1).1.mul (hfi x.2)
  have oF : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → F x * F y = 0 := fun x hx y hy hxy =>
    orthF P ε hfo (memT x hx).1 (memT y hy).1 (by simpa using hxy)
  have inj : Set.InjOn F T := by
    intro x hx y hy hxy
    by_contra hne
    apply (memT x hx).2
    rw [← (idF x hx).eq]
    nth_rewrite 2 [hxy]
    exact oF x hx y hy hne
  refine ⟨⟨T.image F, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨idF x hx, (memT x hx).2⟩
  · intro g hg g' hg' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hg'
    exact oF x hx y hy (fun h => hne (by rw [h]))
  · rw [Finset.sum_image inj, Finset.sum_filter_ne_zero, Finset.sum_product]
    simp only [F]
    simp_rw [← Finset.mul_sum, hfs, mul_one]
    exact P.sum_eq
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    refine ⟨x.1, (memT x hx).1, ?_⟩
    show x.1 * ε x.2 * x.1 = x.1 * ε x.2
    rw [mul_right_comm, (P.idem x.1 (memT x hx).1).1.eq]
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨x.2, by show x.1 * ε x.2 * ε x.2 = x.1 * ε x.2; rw [mul_assoc, (hfi x.2).eq]⟩

variable {B : Type} [CommRing B]

theorem natHom (I : Ideal B) {P Q : PartDiagCut.Part (B ⧸ I)} (h : P ≤ Q) :
    (stageMap I h).comp (βP I P) = βP I Q := by
  refine RingHom.ext fun x => funext fun g => ?_
  simp only [stageMap, βP, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  exact IsLocalization.map_eq _ _

theorem isUnit_comp (I : Ideal B) (Q : PartDiagCut.Part (B ⧸ I)) (g : Q.1) (x : B) (hx : x ∈ S I g.1) :
    IsUnit (βP I Q x g) := by
  simpa [βP] using IsLocalization.map_units (Localization (S I g.1)) (⟨x, hx⟩ : S I g.1)

theorem mem_of_comp (I : Ideal B) (Q : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I Q)
    (hz : ∀ g : Q.1, ∃ w ∈ I.map (βP I Q), ∃ c : Localization (S I g.1), z g = c * w g) :
    z ∈ I.map (βP I Q) := by
  classical
  rw [← Finset.univ_sum_single z]
  refine Ideal.sum_mem _ fun g _ => ?_
  obtain ⟨w, hw, c, hc⟩ := hz g
  have : (Pi.single g (z g) : PiLocalization₂ I Q) = (Pi.single g c : PiLocalization₂ I Q) * w := by
    funext g'
    by_cases hg : g' = g
    · subst hg; simp [hc]
    · simp [hg]
  rw [this]; exact Ideal.mul_mem_left _ _ hw

theorem Lift_of : LateralTheory.E.PartCPf.Lift := by
  classical
  intro B _ I P p a₀ n r f hp hfi hfo hfs hy
  obtain ⟨Q, h, hL⟩ := refine_exists P (fun l => Ideal.Quotient.mk I (f l)) hfi hfo hfs
  choose L hLg using fun g : Q.1 => hL g.1 g.2
  refine ⟨Q, h, fun g => stageMap I h (r (L g)) g, ?_, ?_⟩
  · rw [hp, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, IsRoot.def, eval_prod, eval_sub, eval_X, eval_C]
    funext g
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ (L g)) (by simp)
  · apply mem_of_comp
    intro g
    have hw : βP I Q (f (L g)) * stageMap I h (a₀ - r (L g)) ∈ I.map (βP I Q) := by
      have := Ideal.mem_map_of_mem (stageMap I h) (hy (L g))
      rw [Ideal.map_map, natHom, map_mul, ← RingHom.comp_apply, natHom] at this
      exact this
    have hmem : f (L g) ∈ S I g.1 := ⟨1, by rw [mul_one, mul_comm]; exact hLg g⟩
    obtain ⟨u, hu⟩ := isUnit_comp I Q g (f (L g)) hmem
    refine ⟨_, hw, -(↑u⁻¹ : Localization (S I g.1)), ?_⟩
    simp only [Pi.sub_apply, Pi.mul_apply, map_sub]
    rw [← hu]
    linear_combination (stageMap I h a₀ g - stageMap I h (r (L g)) g) * u.inv_mul

end LateralTheory.E.LiftPf
end
end

section

namespace LateralTheory.E.LZARFacts

theorem LZARStep_of : LateralTheory.E.LZIdemSumNoetherian.LZARStep := by
  intro A _ _ _ M _ _ N P hN
  have : Module.Finite A N := Module.Finite.iff_fg.mpr hN
  set I := IsLocalRing.maximalIdeal A
  set Q : Submodule A N := P.comap N.subtype
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I Q
  refine ⟨c + 1, by omega, ?_⟩
  have hQ : I ^ (c + 1) • (⊤ : Submodule A N) ⊓ Q ≤ I • Q := by
    rw [hc (c + 1) (by omega), show c + 1 - c = 1 by omega, pow_one]
    exact Submodule.smul_mono (le_refl _) inf_le_right
  intro x ⟨hx, hxP⟩
  have hmap : I ^ (c + 1) • N = (I ^ (c + 1) • (⊤ : Submodule A N)).map N.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [hmap] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyQ : y ∈ Q := hxP
  have := hQ ⟨hy, hyQ⟩
  have h2 : (I • Q).map N.subtype ≤ I • P := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono (le_refl _) (Submodule.map_comap_le _ _)
  exact h2 ⟨y, this, rfl⟩

end LateralTheory.E.LZARFacts
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.PointwisePf

def PushColim : Prop := ∀ {D Y' O : CommRingCat.{0}} (φ' : D ⟶ Y') (o : D ⟶ O) {J : Type} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{0}) (t : (Functor.const J).obj D ⟶ F) (s : F ⟶ (Functor.const J).obj O),
  IsColimit (Cocone.mk O s) → (∀ j, t.app j ≫ s.app j = o) →
  ∃ (G : J ⥤ CommRingCat.{0}) (c : Cocone G) (_ : IsColimit c) (u : ∀ j, Y' ⟶ G.obj j) (ψ : ∀ j, F.obj j ⟶ G.obj j)
    (u'' : Y' ⟶ c.pt) (φ'' : O ⟶ c.pt),
    (∀ j, IsPushout φ' (t.app j) (u j) (ψ j)) ∧ (∀ {j k : J} (f : j ⟶ k), u j ≫ G.map f = u k) ∧
    (∀ {j k : J} (f : j ⟶ k), ψ j ≫ G.map f = F.map f ≫ ψ k) ∧ (∀ j, u j ≫ c.ι.app j = u'') ∧
    (∀ j, ψ j ≫ c.ι.app j = s.app j ≫ φ'') ∧ IsPushout φ' o u'' φ''

theorem pc (q : ℕ) (i m : ℤ) {X Y Z : CommRingCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (v : H (ZMod q) (sch.obj (Spec X)) (tw q i) m) :
    pull _ (sch.map (Spec.map g)) (tw q i) m (pull _ (sch.map (Spec.map f)) (tw q i) m v) =
      pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) m v := by
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

theorem unit_of {A B : CommRingCat.{0}} (h : A ⟶ B) (q : ℕ) (hq : IsUnit (q : A)) : IsUnit (q : B) := by
  have := hq.map h.hom; simpa using this

theorem Pointwise_of_pushColim (hPC : PushColim) : LateralTheory.E.KillCokPf.Pointwise := by
  intro hB1 q _ i A Y φ hq D d O o hIE hBC Y' w φ' hpo m y Q hQ
  obtain ⟨J, _, _, F, t, s, hs, ht⟩ := hIE
  have ho : ∀ j, t.app j ≫ s.app j = o := fun j => (ht j).2
  obtain ⟨G, c, hc, u, ψ, u'', φ'', hpj, hu, hψ, hcu, hcψ, hpo''⟩ := hPC φ' o F t s hs ho
  have hRE : RE q i φ'' := hBC _ (w ≫ u'') φ'' (hpo.paste_vert hpo'')
  obtain ⟨z, hz⟩ := (hRE m).2 (pull _ (sch.map (Spec.map u'')) (tw q i) m y)
  obtain ⟨j, zj, hzj⟩ := (hB1 q F (Cocone.mk O s) hs m i).1 z (unit_of (d ≫ o) q hq)
  change pull _ (sch.map (Spec.map (s.app j))) (tw q i) m zj = z at hzj
  let x : H (ZMod q) (sch.obj (Spec (G.obj j))) (tw q i) m :=
    pull _ (sch.map (Spec.map (u j))) (tw q i) m y - pull _ (sch.map (Spec.map (ψ j))) (tw q i) m zj
  have hx0 : pull _ (sch.map (Spec.map (c.ι.app j))) (tw q i) m x = 0 := by
    simp only [x, map_sub, pc, hcu, hcψ, ← hz, ← hzj]
    exact sub_self _
  obtain ⟨k, f, hk⟩ := (hB1 q G c hc m i).2 j x (unit_of (d ≫ t.app j ≫ ψ j) q hq) hx0
  change pull _ (sch.map (Spec.map (G.map f))) (tw q i) m x = 0 at hk
  refine ⟨F.obj k, t.app k, Q.comap (s.app k).hom, (ht k).1, Ideal.comap_isPrime _ _, ?_, G.obj k, u k, ψ k, hpj k,
    pull _ (sch.map (Spec.map (F.map f))) (tw q i) m zj, ?_⟩
  · rw [Ideal.comap_comap, ← ho k]; rfl
  · simp only [x, map_sub, pc, hu, hψ, sub_eq_zero] at hk
    rw [pc, hk]

@[simps]
def dgm {D : CommRingCat.{0}} {J : Type} [SmallCategory J] (F : J ⥤ CommRingCat.{0}) (t : (Functor.const J).obj D ⟶ F) :
    J ⥤ Under D where
  obj j := Under.mk (t.app j)
  map {j k} f := Under.homMk (F.map f) (by simpa using (t.naturality f).symm)
  map_id j := by ext; simp
  map_comp f g := by ext; simp

@[simps]
def cone {D O : CommRingCat.{0}} (o : D ⟶ O) {J : Type} [SmallCategory J] (F : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj D ⟶ F) (s : F ⟶ (Functor.const J).obj O) (ho : ∀ j, t.app j ≫ s.app j = o) :
    Cocone (dgm F t) where
  pt := Under.mk o
  ι := { app j := Under.homMk (s.app j) (by exact ho j)
         naturality j k f := by ext1; exact (s.naturality f).trans (Category.comp_id _) }

theorem pushColim : PushColim := by
  intro D Y' O φ' o J _ _ F t s hs ho
  have : ReflectsColimitsOfShape J (Under.forget D) := reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : (Under.pushout φ').IsLeftAdjoint := ⟨_, ⟨Under.mapPushoutAdj φ'⟩⟩
  have h1 : IsColimit ((Under.forget D).mapCocone (cone o F t s ho)) :=
    IsColimit.ofIsoColimit hs (Cocone.ext (Iso.refl _) (by intro j; exact Category.comp_id _))
  have hK : IsColimit (cone o F t s ho) := isColimitOfReflects (Under.forget D) h1
  have hP := isColimitOfPreserves (Under.pushout φ') hK
  have hc := isColimitOfPreserves (Under.forget Y') hP
  refine ⟨_, _, hc, fun j => pushout.inr (t.app j) φ', fun j => pushout.inl (t.app j) φ', pushout.inr o φ', pushout.inl o φ',
    fun j => (IsPushout.of_hasPushout (t.app j) φ').flip, ?_, ?_, ?_, ?_, (IsPushout.of_hasPushout o φ').flip⟩
  · intro j k f; simp [Under.pushout]; exact pushout.inr_desc _ _ _
  · intro j k f; simp [Under.pushout]; exact pushout.inl_desc _ _ _
  · intro j; simp [Under.pushout]; exact pushout.inr_desc _ _ _
  · intro j; simp [Under.pushout]; exact pushout.inl_desc _ _ _

end LateralTheory.E.PointwisePf

namespace LateralTheory.E.PointwisePf

end LateralTheory.E.PointwisePf
end
end
