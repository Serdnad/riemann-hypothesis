module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle698
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFc
open GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ

instance res_isStrictlyGE (R : Type) [CommRing R] (F : Shv R) : (res R F).IsStrictlyGE 0 := by
  unfold res; infer_instance

instance chains_isStrictlyLE (R : Type) [CommRing R] (E : Spc) : ((chains R).obj E).IsStrictlyLE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)

variable (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
  (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)

theorem phi_δ (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n m : ℤ) (hnm : n + 1 = m)
    (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    phi q V ℓ i (fun j => (z j).1) m (fun j => δ (n - 2 * ((j : ℕ) : ℤ)) (m - 2 * ((j : ℕ) : ℤ)) (α j)) =
      δ n m (phi q V ℓ i (fun j => (z j).1) n α) := by
  have hs : ∀ (f : Fin N → Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n),
      δ n m (∑ j, f j) = ∑ j, δ n m (f j) := fun f => map_sum (AddMonoidHom.mk' (δ n m) (δ_add n m)) f _
  rw [phi_apply, phi_apply, hs]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = δ n m _
  rw [GlobalTheory.T.crossProductTwisted_leibniz_rule V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _)
    (show n - 2 * ((j : ℕ) : ℤ) + 1 = m - 2 * ((j : ℕ) : ℤ) by omega) rfl hnm (by omega) (by omega),
    Cocycle.δ_eq_zero (z j), crossT_zero_right, smul_zero, add_zero]

theorem phi_van (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (p n : ℤ)
    (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)))
    (hα : ∀ j c r hr, p < c → (α j).v c r hr = 0) (c l t : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + n = r) (hc : p < c) :
    (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (phi q V ℓ i z n α).v t r hr = 0 := by
  let ev₀ : Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n →+ _ :=
    AddMonoidHom.mk' (fun γ => (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ γ.v t r hr)
      (fun γ γ' => by rw [Cochain.add_v, Preadditive.comp_add])
  change ev₀ _ = 0

  rw [phi_apply, map_sum]
  exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.cochain_product_vanishing_above_degree V ℓ _ _ (α j) (z j) p (hα j) c l t h r hr hc

theorem pull_iso_bijective {E E' : Spc} (e : E ≅ E') (F : Shv (ZMod q)) (n : ℤ) :
    Function.Bijective (pull (ZMod q) e.hom F n) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨pull (ZMod q) e.inv F n y, ?_⟩⟩
  · have hx := (pull_comp (ZMod q) e.inv e.hom F n x).symm
    have hy := (pull_comp (ZMod q) e.inv e.hom F n y).symm
    rw [e.inv_hom_id, pull_id] at hx hy
    exact hx.symm.trans ((congrArg _ hxy).trans hy)
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem pbf_of_model [NeZero q] (hE : Inv q E)
    (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (hzd : ∀ j : Fin N, CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map
        (bidiag.map ℓ ≫ (bidiagConst B).hom))) (z j) (zero_add _)) =
      pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ)))
    (hzc : ∀ (a : ℕ) (j : Fin N),
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j)
        (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ))
    (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀) : PBF q V := by
  intro n i
  have hf1 := pull_iso_bijective q (twIso E V) (tw q i) n
  have hf2 := pull_awChains_bijective (ZMod q) (twX E V) (res _ (tw q i)) n
  let φ : (∀ j : Fin N, CohomologyClass ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (n - 2 * ((j : ℕ) : ℤ))) → CohomologyClass (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n :=
    fun x => Function.surjInv hf2.2 (pull _ (twIso E V).hom _ n (pbfMap q V n i x))
  have hφ : ∀ (a : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (n - 2 * ((j : ℕ) : ℤ))) (b : Cocycle (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n),
      b.1 = phi q V ℓ i (fun j => (z j).1) n (fun j => (a j).1) →
      φ (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
    intro a b hb
    apply hf2.1
    rw [Function.surjInv_eq hf2.2]
    exact GlobalTheory.T.twisted_cocycle_classes_pullback_cup q V ℓ n i z hzd a b hb
  have hb : Function.Bijective φ :=
    GlobalTheory.ColFilt.bijective_total_of_terms (ZMod q) (biChains (ZMod q) (twX E V))
      (fun p k h => biChains_isZero (twX E V) p k h) ((chains (ZMod q)).obj E)
      (fun j : Fin N => res _ (tw q (i - ((j : ℕ) : ℤ)))) (res _ (tw q i)) (fun j : Fin N => 2 * ((j : ℕ) : ℤ))
      (phi q V ℓ i (fun j => (z j).1)) (fun n m h α => phi_δ q V ℓ i z n m h α)
      (fun p n α hα => phi_van q V ℓ i (fun j => (z j).1) p n α hα)
      (GlobalTheory.T.twisted_cocycle_simplicial_levels_cup q V hE ℓ i z hzc hD) n φ hφ
  have hcomp : (pull _ (twIso E V).hom _ n) ∘ pbfMap q V n i = (cpull (awChains (ZMod q) (twX E V)) (res _ (tw q i)) n) ∘ φ :=
    funext fun x => (Function.surjInv_eq hf2.2 _).symm
  exact (Function.Bijective.of_comp_iff' hf1 _).1 (hcomp ▸ hf2.comp hb)

end GlobalTheory.PBFc

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixIndep

theorem eq_zero_of_locally {X : Scheme.{0}} {U : X.Opens} (s : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), x ∈ W ∧ (X.presheaf.map (homOfLE hW).op).hom s = 0) :
    s = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf U s 0 fun x hx => ?_
  obtain ⟨W, hW, hxW, h0⟩ := h x hx
  have e1 := X.presheaf.germ_res_apply (homOfLE hW) x hxW s
  change (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom 0
  rw [← e1, h0, map_zero, map_zero]

theorem appLE_eq {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f₁ ⁻¹ᵁ U) (a : Γ(Y, U)) :
    (f₁.appLE U V e).hom a = (f₂.appLE U V (h ▸ e)).hom a := by
  subst h; rfl

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V W : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (h : W ≤ V)
    (a : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_appLE {X Y Z : Scheme.{0}} (g : X ⟶ Y) (f : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : W ≤ g ⁻¹ᵁ V) (a : Γ(Z, U)) :
    (g.appLE V W e₂).hom ((f.appLE U V e₁).hom a) =
      ((g ≫ f).appLE U W (fun _ hx => e₁ (e₂ hx))).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.HomFixIndep


open GlobalTheory.HomFixIndep in
theorem GlobalTheory.HomFixIndep.pulled_basis_indep : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (ψA : A'.left ⟶ (topS Rg ⊗ A).left), IsGrpPullback A' A t φA' → ψA ≫ (snd (topS Rg) A).left = φA' → ∀ (d : Fin mA → Γ(Sp R, ⊤)), (∀ (j : Fin 1 → L.ι) (x : A'.left), x ∈ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j → ∃ (W : A'.left.Opens) (hW : W ≤ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j), x ∈ W ∧ ∑ i, (A'.hom.appLE ⊤ W (by simp)).hom (d i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j) W (hW.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j))).hom ((bA i).f j) = 0) → d = 0 := by
  intro Rg _ A _ L k mA bA hB R _ t A' _ φA' ψA hT hψ d hloc
  let t'' : Spec (CommRingCat.of R) ⟶ (topS Rg).left :=
    IsOpenImmersion.lift (⊤ : (Sp Rg).Opens).ι t (by rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial)
  have ht'' : (baseAt t'').hom = t := by simp [t'', baseAt, topS, overRes, baseOver]
  set T := baseAt t'' with hTdef
  have hw : (snd T A).left ≫ A.hom = (fst T A).left ≫ t := by
    rw [← ht'', Over.w (snd T A), Over.w (fst T A)]
  let g : (T ⊗ A).left ⟶ A'.left := hT.1.lift (snd T A).left (fst T A).left hw
  have hg1 : g ≫ φA' = (snd T A).left := hT.1.lift_fst _ _ _
  have hg2 : g ≫ A'.hom = (fst T A).left := hT.1.lift_snd _ _ _
  have hgψ : g ≫ ψA = (homAt t'' ▷ A).left := by
    apply psi_unique
    rw [Category.assoc, hψ, hg1, ← Over.comp_left, whiskerRight_snd]
  let b' : Fin mA → LB.Sec (LPow A L (k : ℤ) T) := fun i =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.pullSecLP A L (k : ℤ) (homAt t'' ▷ A) (whiskerRight_snd (homAt t'') A) (bA i)
  obtain ⟨hli, -⟩ := hB R t'' b' (fun i => ReciprocityTheory.ChartRestriction.G.PullbackSections.isPullSec_pullSecLP A L (k : ℤ) _ _ (bA i))
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  refine hli d ?_ i
  apply Subtype.ext
  funext j
  have hD : (LPow A L (k : ℤ) T).U j ≤ g ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j := by
    intro y hy
    have e : g ≫ ψA ≫ (snd (topS Rg) A).left = (snd T A).left := by
      rw [← Category.assoc, hgψ, ← Over.comp_left, whiskerRight_snd]
    have h1 : (g ≫ ψA ≫ (snd (topS Rg) A).left).base y ∈ (L.U (j 0) : Set A.left) := by
      rw [e]; exact Set.mem_iInter.1 hy 0
    exact Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h1
  have hF : (∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j) (by simp)).hom (d i) *
      (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
        (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j)
        (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j)).hom ((bA i).f j)) = 0 := by
    refine eq_zero_of_locally _ fun x hx => ?_
    obtain ⟨W, hW, hxW, h0⟩ := hloc j x hx
    refine ⟨W, hW, hxW, ?_⟩

    rw [map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h0
    rw [map_mul]
    exact congrArg₂ (· * ·) (res_appLE _ _ _ _ _ _ _) (res_appLE _ _ _ _ _ _ _)
  calc (∑ i, d i • SecM.ofSec A (b' i)).val j
      = ∑ i, ((fst T A).left.appLE ⊤ ((LPow A L (k : ℤ) T).U j) (by simp)).hom (d i) *
          ((homAt t'' ▷ A).left.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
            ((LPow A L (k : ℤ) T).U j) (chart_le_res A L _ (whiskerRight_snd (homAt t'') A) _ j)).hom ((bA i).f j) := by
        rw [Submodule.coe_sum, Finset.sum_apply]
        rfl
    _ = (g.appLE _ _ hD).hom (∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j) (by simp)).hom (d i) *
      (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j)
        (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j)
        (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j)).hom ((bA i).f j)) := by

        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        exact congrArg₂ (· * ·) (((appLE_appLE _ _ _ _ _ _ _ _).trans (appLE_eq hg2 _ _ _ _)).symm)
          (((appLE_appLE _ _ _ _ _ _ _ _).trans (appLE_eq hgψ _ _ _ _)).symm)
    _ = _ := by rw [hF, map_zero]; rfl
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem isLift_of_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N' s') (f : S' ⟶ S) (om : ObjMap (o'.forget N hd hc) o f) (T : Over S) (g : T.left ⟶ S') (lv : D.La → (T ⟶ o.A)), g ≫ f = T.hom → (∀ a, (lv a).left = g ≫ (o'.eta a).left ≫ om.φ) → IsLift o N' T lv := by
  intro p _ D R _ b N N' hd hc S S' s s' o o' f om T g lv hT hlv
  obtain ⟨T, ⟨⟨⟩⟩, h⟩ := T
  change T ⟶ S' at g
  replace hT : (g ≫ f : T ⟶ S) = h := hT
  subst hT
  obtain ⟨φ, hφ⟩ : ∃ φ : o'.A.left ⟶ o.A.left, φ = om.φ := ⟨om.φ, rfl⟩
  have hlv' : ∀ a, (lv a).left = g ≫ (o'.eta a).left ≫ φ := fun a => by rw [hφ]; exact hlv a
  have cart : IsGrpPullback o'.A o.A f φ := by rw [hφ]; exact om.cart
  have sq : IsSquare φ om.φ₂ := by rw [hφ]; exact om.sq
  have ha : ∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left := fun c => by rw [hφ]; exact om.act c
  have he : ∀ x, (o'.eta ((N' / N) • x)).left ≫ φ = f ≫ (o.eta x).left := fun x => by rw [hφ]; exact om.eta x
  let T' : Over S' := Over.mk g
  let q : D.La → (T' ⟶ o'.A) := fun a => toUnit T' ≫ o'.eta a
  have hq : ∀ a, (q a).left = g ≫ (o'.eta a).left := fun a => by
    simp only [q, Over.comp_left, Over.toUnit_left]
    rfl
  have key : ∀ a, (lv a).left = (q a).left ≫ φ := fun a => by rw [hlv', hq, Category.assoc]
  have mulx : ∀ x y : D.La, (lv x * lv y).left = (q x * q y).left ≫ φ := fun x y =>
    cart.2 T' (q x) (q y) (lv x) (lv y) (key x) (key y)
  refine ⟨fun x y => ?_, fun x => ?_, fun c x => ?_, fun x => ?_, fun k _ _ x => ?_⟩
  · apply Over.OverMorphism.ext
    rw [mulx, key]
    congr 1
    show (toUnit T' ≫ o'.eta (x + y)).left = (toUnit T' ≫ o'.eta x * toUnit T' ≫ o'.eta y).left
    rw [o'.eta_add, MonObj.comp_mul]
  · have h1 : q (N' • x) = 1 := by
      show toUnit T' ≫ o'.eta (N' • x) = 1
      rw [o'.eta_ker, MonObj.comp_one]
    have hzz : lv (N' • x) * lv (N' • x) = lv (N' • x) * 1 := by
      rw [_root_.mul_one]
      apply Over.OverMorphism.ext
      rw [mulx, key, h1, _root_.mul_one]
    exact mul_left_cancel hzz
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, hlv', hlv', o'.eta_lin, Over.comp_left]
    simp only [Category.assoc, ha]
  · apply Over.OverMorphism.ext
    rw [hlv', he, Over.comp_left, Over.toUnit_left]
    exact (Category.assoc _ _ _).symm
  · obtain ⟨I', hI'⟩ := o'.geom k (x ≫ g) (Spec.preimage ((x ≫ g) ≫ s')).hom (Spec.map_preimage _).symm
    have h3 := (GlobalTheory.T.tateSimilitude_prime_to_p_pullback_square p D R b N N' S S' s s' o o' f φ om.φ₂ cart sq ha om.pol k (x ≫ g)).1 I'
    rw [Category.assoc] at h3
    obtain ⟨I, hI⟩ := h3
    refine ⟨I, fun y => ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hI, ← hI' y, Over.comp_left, Over.toUnit_left]
    change x ≫ (lv y).left = _
    rw [hlv']
    simp only [Over.mk_hom, Category.assoc]

end GlobalTheory.UPel.HT
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixNorm

theorem gs_finsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (s : Finset κ)
    (a : κ → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem gs_npow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem one_comp_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G]
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom hφ (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem stalkMap_gm_pow {Z Y : Scheme.{0}} (t : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : t z ∈ V) (a : Γ(Y, V)ˣ) (n : ℕ) :
    (t.stalkMap z).hom ((gm (𝟙 Y) (t z) V a) ^ n).val = gs t z V a.val ^ n := by
  rw [Units.val_pow_eq_pow_val, ← gs_unit (𝟙 Y) (t z) V h, map_pow, ← gs_stalkMap t z V h]

theorem norm_at_zero : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)ˣ), (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Normal t c αA βB → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ (φB' ≫ GlobalTheory.HomFixUniv.θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p) (by simp)).hom (c i j) *
          ((φA' ≫ GlobalTheory.HomFixUniv.θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (u p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c u hcov hA hB hT hN hrel p
  obtain ⟨gA, gB, hΦ, -⟩ := hT
  haveI : IsMonHom Φ' := hΦ
  have e₀ : zeroPt A' ≫ A'.hom = 𝟙 _ := by simp [zeroPt]
  have eΦ : zeroPt A' ≫ Φ'.left = zeroPt B' := by rw [zeroPt, zeroPt, ← Over.comp_left, IsMonHom.one_hom]
  have eA' : zeroPt A' ≫ φA' ≫ θ A = t ≫ eSec A ≫ θ A := by
    rw [← Category.assoc, zeroPt, one_comp_of_isGrpPullback gA, Category.assoc]; rfl
  have eB' : zeroPt A' ≫ Φ'.left ≫ φB' ≫ θ B = t ≫ eSec B ≫ θ B := by
    rw [← Category.assoc, eΦ, ← Category.assoc, zeroPt, one_comp_of_isGrpPullback gB, Category.assoc]; rfl
  refine fn_ext fun z hz => ?_

  have hz0 := hz
  obtain ⟨⟨hzU', hzA'⟩, hzB'⟩ := hz
  have hzU : zeroPt A' z ∈ (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p := hzU'
  have hzA : t z ∈ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) := hzA'
  have hzB : t z ∈ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0) := hzB'
  have pA : eSec A (t z) ∈ L.U (p.2 0) := Set.mem_iInter.1 hzA PUnit.unit
  have pB : eSec B (t z) ∈ M.U (p.1 0) := Set.mem_iInter.1 hzB PUnit.unit
  have mA : (eSec A ≫ θ A) (t z) ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 := by
    refine Set.mem_iInter.2 fun i => ?_
    show (snd (topS Rg) A).left ((eSec A ≫ θ A) (t z)) ∈ L.U (p.2 i)
    rw [← Scheme.Hom.comp_apply, Category.assoc, θ_snd, Category.comp_id, Subsingleton.elim i 0]
    exact pA
  have mB : (eSec B ≫ θ B) (t z) ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 := by
    refine Set.mem_iInter.2 fun i => ?_
    show (snd (topS Rg) B).left ((eSec B ≫ θ B) (t z)) ∈ M.U (p.1 i)
    rw [← Scheme.Hom.comp_apply, Category.assoc, θ_snd, Category.comp_id, Subsingleton.elim i 0]
    exact pB
  have sB : ∀ j, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      (((Φ'.left ≫ (φB' ≫ θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1)) =
        gs t z ⊤ (βB j) * gs t z (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0)) (eB.s (fun _ => p.1 0)).val ^ k := by
    intro j
    have v := hB j (t z) p.1 mB
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [eB']
    erw [gs_comp t _ z _ mB]
    erw [v]
    simp only [GlobalTheory.HomFixUniv.uFr]
    rw [map_mul]
    erw [stalkMap_gm_pow t z _ hzB, ← gs_stalkMap t z ⊤ trivial]
  have sA : ∀ i, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      (((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) =
        gs t z ⊤ (αA i) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k := by
    intro i
    have v := hA i (t z) p.2 mA
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [eA']
    erw [gs_comp t _ z _ mA]
    erw [v]
    simp only [GlobalTheory.HomFixUniv.uFr]
    rw [map_mul]
    erw [stalkMap_gm_pow t z _ hzA, ← gs_stalkMap t z ⊤ trivial]
  have sC : ∀ i j, gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
      ((A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (by simp)).hom (c i j)) =
        gs (𝟙 _) z ⊤ (c i j) := by
    intro i j
    erw [gs_appLE _ _ _ _ _ _ hzU]
    rw [e₀]
  have gt : ∀ x : Γ(Sp Rg, ⊤), gs t z ⊤ x = gs (𝟙 _) z ⊤ (t.appTop x) := by
    intro x
    have e := gs_pull (𝟙 (Sp R)) t z ⊤ trivial x
    rw [Category.id_comp] at e
    exact e.symm
  have nN : ∀ j, ∑ i, gs (𝟙 _) z ⊤ (c i j) * gs t z ⊤ (αA i) = gs t z ⊤ (βB j) := by
    intro j
    rw [gt, hN j, gs_finsum _ z ⊤ trivial]
    exact Finset.sum_congr rfl fun i _ => by rw [gt, gs_mul _ z ⊤ trivial]
  have hcz : (eSec B ≫ θ B) (t z) ∈ (⨆ j, nonzeroLocus (bB j)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hcz
  have hu := (GlobalTheory.mem_nonzeroLocus_iff_pull (bB j) (eSec B ≫ θ B) (t z) mB).1 hj
  erw [hB j (t z) p.1 mB] at hu
  have hβ : IsUnit (gs t z ⊤ (βB j)) := by
    rw [gs_stalkMap t z ⊤ trivial]
    exact (isUnit_of_mul_isUnit_left hu).map _
  have E := congrArg (gs (zeroPt A') z ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)) (hrel j p)
  rw [sB j, gs_mul _ _ _ hzU, gs_finsum _ _ _ hzU] at E
  simp only [gs_mul _ _ _ hzU, sC, sA] at E
  have hs : ∑ i, gs (𝟙 _) z ⊤ (c i j) * (gs t z ⊤ (αA i) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k) =
      (∑ i, gs (𝟙 _) z ⊤ (c i j) * gs t z ⊤ (αA i)) * gs t z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0)) (eA.s (fun _ => p.2 0)).val ^ k := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  rw [hs, nN j] at E
  rw [gs_mul _ z _ hz0, gs_npow _ z _ hz0, gs_npow _ z _ hz0]
  erw [gs_appLE _ _ _ _ _ _ hz0, gs_appLE _ _ _ _ _ _ hz0, gs_appLE _ _ _ _ _ _ hz0]
  simp only [Category.id_comp]
  exact hβ.mul_left_cancel (by rw [E]; ring)

end GlobalTheory.HomFixNorm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis : ∀ (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k mB : ℕ) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))), IsAbelianScheme B → M.IsLB → 1 ≤ k → VeryAmpleAt B M k → IsBCBasis B M k bB → GlobalTheory.AmpleSpan.EmbedsBy (GlobalTheory.HomFixUniv.fA B) bB := by
  first | (exact @GlobalTheory.HomFixUniv.embedsBy_fA_of_isBCBasis) | (exact GlobalTheory.HomFixUniv.embedsBy_fA_of_isBCBasis) | (intros; apply GlobalTheory.HomFixUniv.embedsBy_fA_of_isBCBasis  <;> assumption)
end
