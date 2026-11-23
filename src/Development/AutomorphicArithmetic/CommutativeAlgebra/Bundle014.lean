module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.EtaleCohomology.EtaleSheaves.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import GroundTheory.FunctionField.PlaceDefs

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.DegreeAdditivity

private theorem D_add {C : DC} (n : ℤ) (x y : C.Tot) : C.D n (x + y) = C.D n x + C.D n y := by
  funext p t
  rcases p with _ | p
  · simp [DC.D, map_add (f := _)]
  · simp only [DC.D, Pi.add_apply, map_add (f := _), smul_add]
    abel

private theorem D_sub {C : DC} (n : ℤ) (x y : C.Tot) : C.D n (x - y) = C.D n x - C.D n y := by
  funext p t
  rcases p with _ | p
  · simp [DC.D, map_sub]
  · simp only [DC.D, Pi.sub_apply, map_sub, smul_sub]
    abel

private theorem D_zero {C : DC} (n : ℤ) : C.D n (0 : C.Tot) = 0 := by
  funext p t
  rcases p with _ | p <;> simp [DC.D]

private theorem Deg_zero {C : DC} {n : ℤ} : C.Deg n (0 : C.Tot) := fun _ _ _ => rfl

private theorem Deg_add {C : DC} {n : ℤ} {x y : C.Tot} (hx : C.Deg n x) (hy : C.Deg n y) :
    C.Deg n (x + y) := fun p s h => by
  change x p s + y p s = 0
  rw [hx p s h, hy p s h, add_zero]

private theorem Deg_sub {C : DC} {n : ℤ} {x y : C.Tot} (hx : C.Deg n x) (hy : C.Deg n y) :
    C.Deg n (x - y) := fun p s h => by
  change x p s - y p s = 0
  rw [hx p s h, hy p s h, sub_zero]

private theorem tot_add {C C' : DC} (Φ : C.Hom C') (x y : C.Tot) :
    Φ.tot (x + y) = Φ.tot x + Φ.tot y := by
  funext p s
  exact map_add _ _ _

private theorem tot_sub {C C' : DC} (Φ : C.Hom C') (x y : C.Tot) :
    Φ.tot (x - y) = Φ.tot x - Φ.tot y := by
  funext p s
  exact map_sub _ _ _

private theorem tot_zero {C C' : DC} (Φ : C.Hom C') : Φ.tot (0 : C.Tot) = 0 := by
  funext p s
  exact map_zero _

private theorem Deg_tot {C C' : DC} (Φ : C.Hom C') {n : ℤ} {x : C.Tot} (h : C.Deg n x) :
    C'.Deg n (Φ.tot x) := fun p s hne => by
  change Φ p s (x p s) = 0
  rw [h p s hne, map_zero]

private theorem hom_d {C C' : DC} {Φ : C.Hom C'} (h : Φ.Ok) (p : ℕ) (s t : ℤ) (e : t = s + 1)
    (x : C.A p s) : Φ p t (C.d p s t x) = C'.d p s t (Φ p s x) := by
  subst e
  exact h.1 p s x

private theorem tot_D {C C' : DC} {Φ : C.Hom C'} (h : Φ.Ok) (n : ℤ) (x : C.Tot) :
    Φ.tot (C.D n x) = C'.D n (Φ.tot x) := by
  funext p t
  rcases p with _ | p
  · simp only [DC.D, DC.Hom.tot]
    exact hom_d h 0 (t - 1) t (by ring) _
  · simp only [DC.D, DC.Hom.tot, map_add (f := _), Units.smul_def, map_zsmul]
    rw [hom_d h (p + 1) (t - 1) t (by ring), h.2]

private theorem rel_zero {C : DC} {n : ℤ} {H : Type 1} [AddCommGroup H] {rel : C.Tot → H → Prop}
    (h : TModel C n rel) : rel 0 0 := by
  obtain ⟨x, -, -, r⟩ := h.surj 0
  have := h.sub x 0 x 0 r r
  simpa using this

end UpperTheory.DegreeAdditivity

open UpperTheory.DegreeAdditivity in
theorem UpperTheory.bijective_iff_totalQuasiIso_of_totalModels :
    ∀ (C C' : DC) (Φ : C.Hom C'), C.Ok → C'.Ok → Φ.Ok → ∀ (H H' : ℤ → Type 1) [∀ n, AddCommGroup (H n)] [∀ n, AddCommGroup (H' n)] (rel : ∀ n, C.Tot → H n → Prop) (rel' : ∀ n, C'.Tot → H' n → Prop) (F : ∀ n, H n → H' n),
    (∀ n, TModel C n (rel n)) → (∀ n, TModel C' n (rel' n)) → (∀ n x a, rel n x a → rel' n (Φ.tot x) (F n a)) → ((∀ n, Function.Bijective (F n)) ↔ Φ.TotEx) := by
  intro C C' Φ hC hC' hΦ H H' _ _ rel rel' F hM hM' hF
  constructor
  · intro hbij n a y ha hy hDa hΦa
    obtain ⟨ca, ra⟩ := (hM (n + 1)).ex a ha hDa
    have r0 : rel' (n + 1) 0 (F (n + 1) 0) := by
      have := hF (n + 1) 0 0 (rel_zero (hM (n + 1)))
      rwa [tot_zero] at this
    have hF0 : F (n + 1) 0 = 0 :=
      ((hM' (n + 1)).zero 0 (F (n + 1) 0) Deg_zero r0).2 ⟨0, Deg_zero, D_zero _⟩
    have hFa : F (n + 1) ca = 0 := by
      refine ((hM' (n + 1)).zero _ _ (Deg_tot Φ ha) (hF (n + 1) a ca ra)).2 ⟨y, ?_, ?_⟩
      · simpa using hy
      · simpa using hΦa.symm
    have hca : ca = 0 := (hbij (n + 1)).1 (hFa.trans hF0.symm)
    obtain ⟨a', ha', hDa'⟩ := ((hM (n + 1)).zero a ca ha ra).1 hca
    simp only [add_sub_cancel_right] at ha' hDa'
    have hz : C'.Deg n (y - Φ.tot a') := Deg_sub hy (Deg_tot Φ ha')
    have hDz : C'.D n (y - Φ.tot a') = 0 := by
      rw [D_sub, ← tot_D hΦ, hDa', hΦa, sub_self]
    obtain ⟨cz, rz⟩ := (hM' n).ex _ hz hDz
    obtain ⟨c, hc⟩ := (hbij n).2 cz
    obtain ⟨w, hw, hDw, rw⟩ := (hM n).surj c
    have r2 := (hM' n).sub _ _ _ _ rz (hF n w c rw)
    rw [hc, sub_self] at r2
    obtain ⟨y', hy', hDy'⟩ :=
      ((hM' n).zero _ _ (Deg_sub hz (Deg_tot Φ hw)) r2).1 rfl
    refine ⟨a' + w, y', Deg_add ha' hw, hy', ?_, ?_⟩
    · rw [D_add, hDa', hDw, add_zero]
    · rw [tot_add, hDy']
      abel
  · intro hT m
    constructor
    · intro c1 c2 h12
      obtain ⟨x1, hx1, hD1, r1⟩ := (hM m).surj c1
      obtain ⟨x2, hx2, hD2, r2⟩ := (hM m).surj c2
      have r12 := (hM m).sub _ _ _ _ r1 r2
      have r12' := (hM' m).sub _ _ _ _ (hF m _ _ r1) (hF m _ _ r2)
      rw [h12, sub_self, ← tot_sub] at r12'
      obtain ⟨y, hy, hDy⟩ :=
        ((hM' m).zero _ 0 (Deg_tot Φ (Deg_sub hx1 hx2)) r12').1 rfl
      obtain ⟨a', -, ha', -, hDa', -⟩ := hT (m - 1) (x1 - x2) y
        (by simpa using Deg_sub hx1 hx2) hy
        (by rw [sub_add_cancel, D_sub, hD1, hD2, sub_self]) hDy.symm
      exact sub_eq_zero.mp (((hM m).zero _ _ (Deg_sub hx1 hx2) r12).2 ⟨a', ha', hDa'⟩)
    · intro c'
      obtain ⟨y, hy, hDy, ry⟩ := (hM' m).surj c'
      obtain ⟨a', y', ha', hy', hDa', hyeq⟩ :=
        hT m 0 y Deg_zero hy (D_zero _) (by rw [tot_zero, hDy])
      obtain ⟨c, rc⟩ := (hM m).ex a' ha' hDa'
      refine ⟨c, ?_⟩
      have r := (hM' m).sub _ _ _ _ ry (hF m _ _ rc)
      have h0 : c' - F m c = 0 :=
        ((hM' m).zero _ _ (Deg_sub hy (Deg_tot Φ ha')) r).2 ⟨y', hy', by rw [hyeq]; abel⟩
      exact (sub_eq_zero.mp h0).symm
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.ExtensionByZero

private noncomputable def ext0 (C : DC) (s : ℤ) (a : C.A 0 s) : C.Tot
  | 0, t => (Pi.single s a : ∀ t, C.A 0 t) t
  | _ + 1, _ => 0

private theorem extByZero_same (C : DC) (s : ℤ) (a : C.A 0 s) : ext0 C s a 0 s = a :=
  Pi.single_eq_same (M := fun t => C.A 0 t) s a

private theorem unitCharacterExtendByZero_ne_zero_of_isUnit (C : DC) (s : ℤ) (a : C.A 0 s) {t : ℤ} (h : t ≠ s) : ext0 C s a 0 t = 0 :=
  Pi.single_eq_of_ne (M := fun t => C.A 0 t) h a

private theorem extByZero_succ (C : DC) (s : ℤ) (a : C.A 0 s) (p : ℕ) (t : ℤ) : ext0 C s a (p + 1) t = 0 := rfl

private theorem extByZero_degree (C : DC) (s : ℤ) (a : C.A 0 s) : C.Deg s (ext0 C s a) := by
  intro p t h
  rcases p with _ | p
  · exact unitCharacterExtendByZero_ne_zero_of_isUnit C s a (fun e => h (by simp [e]))
  · rfl

private theorem d_idx (C : DC) (f : ∀ t, C.A 0 t) {u s : ℤ} (t : ℤ) (h : u = s) :
    C.d 0 u t (f u) = C.d 0 s t (f s) := by
  subst h; rfl

end UpperTheory.ExtensionByZero

open UpperTheory.ExtensionByZero in
theorem UpperTheory.columnExact_zero_of_totalExact_of_vertical_zero :
    ∀ (C C' : DC) (Φ : C.Hom C'), (∀ s x, C.δ 0 s x = 0) → (∀ s x, C'.δ 0 s x = 0) → Φ.TotEx → Φ.ColEx 0 := by
  intro C C' Φ h0 h0' hT s a y hda hΦ
  have hD : C.D (s + 1) (ext0 C (s + 1) a) = 0 := by
    funext p t
    rcases p with _ | p
    · change C.d 0 (t - 1) t (ext0 C (s + 1) a 0 (t - 1)) = 0
      by_cases h : t - 1 = s + 1
      · obtain rfl : t = s + 1 + 1 := by omega
        rw [d_idx C (ext0 C (s + 1) a 0) _ h, extByZero_same]
        exact hda
      · rw [unitCharacterExtendByZero_ne_zero_of_isUnit C _ a h, map_zero]
    · change C.d (p + 1) (t - 1) t (ext0 C (s + 1) a (p + 1) (t - 1)) +
        (s + 1 + 1).negOnePow • C.δ p t (ext0 C (s + 1) a p t) = 0
      rw [extByZero_succ, map_zero, zero_add]
      rcases p with _ | p
      · rw [h0, smul_zero]
      · rw [extByZero_succ, map_zero, smul_zero]
  have hE : Φ.tot (ext0 C (s + 1) a) = C'.D s (ext0 C' s y) := by
    funext p t
    rcases p with _ | p
    · change Φ 0 t (ext0 C (s + 1) a 0 t) = C'.d 0 (t - 1) t (ext0 C' s y 0 (t - 1))
      by_cases h : t = s + 1
      · subst h
        rw [d_idx C' (ext0 C' s y 0) _ (by omega : s + 1 - 1 = s), extByZero_same, extByZero_same]
        exact hΦ
      · rw [unitCharacterExtendByZero_ne_zero_of_isUnit C _ a h, unitCharacterExtendByZero_ne_zero_of_isUnit C' _ y (fun e => h (by omega)), map_zero, map_zero]
    · change Φ (p + 1) t (ext0 C (s + 1) a (p + 1) t) =
        C'.d (p + 1) (t - 1) t (ext0 C' s y (p + 1) (t - 1)) +
          (s + 1).negOnePow • C'.δ p t (ext0 C' s y p t)
      rw [extByZero_succ, extByZero_succ, map_zero, map_zero, zero_add]
      rcases p with _ | p
      · rw [h0', smul_zero]
      · rw [extByZero_succ, map_zero, smul_zero]
  obtain ⟨a', y', -, -, h1, h2⟩ :=
    hT s (ext0 C (s + 1) a) (ext0 C' s y) (extByZero_degree C _ a) (extByZero_degree C' _ y) hD hE
  refine ⟨a' 0 s, y' 0 (s - 1), ?_, ?_⟩
  · have h := congrFun (congrFun h1 0) (s + 1)
    change C.d 0 (s + 1 - 1) (s + 1) (a' 0 (s + 1 - 1)) = ext0 C (s + 1) a 0 (s + 1) at h
    rw [d_idx C (a' 0) _ (by omega : s + 1 - 1 = s), extByZero_same] at h
    exact h
  · have h := congrFun (congrFun h2 0) s
    rw [show ext0 C' s y 0 s = y from extByZero_same C' s y] at h
    exact h
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem map_res' {E E' : Spc} (j : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (z : Sx E p U) :
    (z.map j).res g = (z.res g).map j := by
  exact (ConcreteCategory.congr_hom ((j.app _).naturality g.op) z).symm

private theorem map_face' {E E' : Spc} (j : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (z : Sx E (p + 1) U) (i : Fin (p + 2)) :
    (z.map j).face i = (z.face i).map j :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (j.naturality (SimplexCategory.δ i).op) (op U)) z).symm

private theorem ev_delta_zero {R : Type} [CommRing R] {E : Spc} {I : Cx R} {N M s t : ℤ} (hm : N + 1 = M)
    (α : Cochain ((chains R).obj E) I N) (U : Scheme.{0}) (x : Sx E 0 U)
    (ht : -((0 : ℕ) : ℤ) + M = t) (hs : -((0 : ℕ) : ℤ) + N = s) :
    ev (R := R) (δ N M α) 0 t ht U x = Sec.map (I.d s t) (ev (R := R) α 0 s hs U x) := by
  obtain rfl : t = M := by omega
  obtain rfl : s = N := by omega
  exact (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R hm α U).1 x

private theorem fam_smul_apply {R : Type} [CommRing R] {E : Spc} {Z : Sub E} {p : ℕ} {M : Shv R} (u : ℤˣ) (a : Fam Z p M)
    (U : Scheme.{0}) (z : Sx E p U) : (u • a).1 U z = u • a.1 U z := by
  rfl

theorem UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain :
    ∀ (R : Type) [CommRing R] {E E' : Spc} (j : E ⟶ E') (Z : Sub E) (K : Cx R) (m n N : ℤ), n + m = N →
    (∀ γ : Cochain ((chains R).obj E') K N, (∀ (p : ℕ) (s : ℤ) h (U : Scheme.{0}) (z : Sx E p U), Z.mem p U z → ev (R := R) γ p s h U (z.map j) = 0) → ∃ x : (famDC Z K m).Tot, (famDC Z K m).Deg n x ∧ Comp j γ x) ∧
    (∀ (γ : Cochain ((chains R).obj E') K N) (x x' : (famDC Z K m).Tot), (famDC Z K m).Deg n x → (famDC Z K m).Deg n x' → Comp j γ x → Comp j γ x' → x = x') ∧
    (∀ (γ : Cochain ((chains R).obj E') K N) (x : (famDC Z K m).Tot), Comp j γ x → Comp j (δ N (N + 1) γ) ((famDC Z K m).D n x)) ∧
    (∀ (γ γ' : Cochain ((chains R).obj E') K N) (x x' : (famDC Z K m).Tot), Comp j γ x → Comp j γ' x' → Comp j (γ - γ') (x - x')) ∧
    ∀ x : (famDC Z K m).Tot, (famDC Z K m).Deg n x → (famDC Z K m).Deg (n + 1) ((famDC Z K m).D n x) := by
  intro R _ E E' j Z K m n N hN
  have ev_nat := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E') (I := K) (n := N)).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    let x : (famDC Z K m).Tot := fun p s =>
      if h : -(p : ℤ) + N = s + m then
        (⟨fun U z => ev (R := R) γ p (s + m) h U (z.map j),
          ⟨fun V U g z => (ev_nat γ p (s + m) h V U g (z.map j)).trans (by rw [map_res']),
           fun U z hz => hγ p (s + m) h U z hz⟩⟩ : Fam Z p (K.X (s + m)))
      else 0
    refine ⟨x, fun p s hps => ?_, fun p s h U z => ?_⟩
    · have h : ¬ (-(p : ℤ) + N = s + m) := by omega
      exact dif_neg h
    · exact congrArg (fun a : Fam Z p (K.X (s + m)) =>
        (a : (U : Scheme.{0}) → Sx E p U → Sec (K.X (s + m)) U) U z) (dif_pos h)
  · intro γ x x' hx hx' cx cx'
    funext p s
    by_cases hps : (p : ℤ) + s = n
    · have h : -(p : ℤ) + N = s + m := by omega
      change (x p s : Fam Z p (K.X (s + m))) = x' p s
      apply Subtype.ext
      funext U z
      exact (cx p s h U z).trans (cx' p s h U z).symm
    · rw [hx p s hps, hx' p s hps]
  · intro γ x cx p s h U z
    rcases p with _ | p
    · have h0 : -((0 : ℕ) : ℤ) + N = (s - 1) + m := by omega
      rw [ev_delta_zero (s := s - 1 + m) rfl γ U (z.map j) h h0, ← cx 0 (s - 1) h0 U z]
      rfl
    · have hs : -((p + 1 : ℕ) : ℤ) + N = (s - 1) + m := by omega
      have hp : -(p : ℤ) + N = s + m := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R (rfl : N + 1 = N + 1) γ U).2 p (s - 1 + m) (s + m) hs h (z.map j),
        ← cx (p + 1) (s - 1) hs U z]
      simp only [map_face']
      rw [Finset.sum_congr rfl (fun i _ => by rw [← cx p s hp U (z.face i)])]
      have eN : (N + 1).negOnePow = (n + 1).negOnePow * m.negOnePow := by
        rw [← Int.negOnePow_add]; congr 1; omega
      have e2 := fam_smul_apply (n + 1).negOnePow
        (Fam.δ Z p (K.X (s + m)) m.negOnePow (x p s : Fam Z p (K.X (s + m)))) U z
      rw [eN, mul_smul]
      show Sec.map (K.d (s - 1 + m) (s + m)) ((x (p + 1) (s - 1) : Fam Z (p + 1) (K.X (s - 1 + m))).1 U z) +
        ((n + 1).negOnePow • Fam.δ Z p (K.X (s + m)) m.negOnePow (x p s : Fam Z p (K.X (s + m)))).1 U z = _
      rw [e2]
      rfl
  · intro γ γ' x x' cx cx' p s h U z
    rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E') (I := K) (n := N)).1 γ γ' p (s + m) h U (z.map j)).2.1,
      ← cx p s h U z, ← cx' p s h U z]
    rfl
  · intro x hx p s hps
    rcases p with _ | p
    · have h1 : ((0 : ℕ) : ℤ) + (s - 1) ≠ n := by omega
      show (Fam.map Z 0 (K.d (s - 1 + m) (s + m))) (x 0 (s - 1)) = 0
      rw [hx 0 (s - 1) h1]
      exact map_zero _
    · have h1 : ((p + 1 : ℕ) : ℤ) + (s - 1) ≠ n := by omega
      have h2 : (p : ℤ) + s ≠ n := by omega
      show (Fam.map Z (p + 1) (K.d (s - 1 + m) (s + m))) (x (p + 1) (s - 1)) +
        (n + 1).negOnePow • (Fam.δ Z p (K.X (s + m)) m.negOnePow) (x p s) = 0
      rw [hx _ _ h1, hx _ _ h2]
      show (Fam.map Z (p + 1) (K.d (s - 1 + m) (s + m))) (0 : Fam Z (p + 1) (K.X (s - 1 + m))) +
        (n + 1).negOnePow • (Fam.δ Z p (K.X (s + m)) m.negOnePow) (0 : Fam Z p (K.X (s + m))) = 0
      rw [map_zero, map_zero, smul_zero, add_zero]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.PushoutCovers

private noncomputable def Fe (p : ℕ) (U : Scheme.{0}) : Spc ⥤ Type 1 :=
  ((evaluation _ _).obj (op (SimplexCategory.mk p))) ⋙ ((evaluation _ _).obj (op U)) ⋙ uliftFunctor.{1, 0}

private theorem po (P : Arrow Spc) (p : ℕ) (U : Scheme.{0}) :
    IsPushout ((Fe p U).map P.hom) ((Fe p U).map P.hom) ((Fe p U).map (dbl.inl P)) ((Fe p U).map (dbl.inr P)) := by
  have : PreservesColimit (span P.hom P.hom) (Fe p U) := by
    unfold Fe
    infer_instance
  exact (IsPushout.of_hasPushout P.hom P.hom).map (Fe p U)

private theorem cover (P : Arrow Spc) (p : ℕ) (U : Scheme.{0}) (w : Sx (dbl P) p U) :
    (∃ z : Sx P.right p U, z.map (dbl.inl P) = w) ∨ ∃ z : Sx P.right p U, z.map (dbl.inr P) = w := by
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit (po P p U).isColimit (ULift.up w)
  rcases j with _ | j
  · left
    exact ⟨Sx.map P.hom y.down, congrArg ULift.down hy⟩
  · cases j
    · left
      exact ⟨y.down, congrArg ULift.down hy⟩
    · right
      exact ⟨y.down, congrArg ULift.down hy⟩

private theorem fn (P : Arrow Spc) (p : ℕ) (U : Scheme.{0}) {T : Type 1} [Zero T] (f : Sx P.right p U → T)
    (hf : ∀ y : Sx P.left p U, f (y.map P.hom) = 0) :
    ∃ φ : Sx (dbl P) p U → T, (∀ z : Sx P.right p U, φ (z.map (dbl.inl P)) = f z) ∧ ∀ z : Sx P.right p U, φ (z.map (dbl.inr P)) = 0 := by
  have h := po P p U
  let d : (Fe p U).obj (dbl P) ⟶ T :=
    h.desc (TypeCat.ofHom fun z => f z.down) (TypeCat.ofHom fun _ => 0) (by
      ext y
      exact hf y.down)
  refine ⟨fun w => d (ULift.up w), fun z => ?_, fun z => ?_⟩
  · exact ConcreteCategory.congr_hom (CC := fun X => X) (h.inl_desc _ _ _)
      (ULift.up z : ULift.{1} (Sx P.right p U))
  · exact ConcreteCategory.congr_hom (CC := fun X => X) (h.inr_desc _ _ _)
      (ULift.up z : ULift.{1} (Sx P.right p U))

private theorem res_map {E E' : Spc} (f : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (z : Sx E p U) :
    (z.map f).res g = (z.res g).map f := by
  exact (ConcreteCategory.congr_hom (CC := fun X => X) ((f.app _).naturality g.op) z).symm

end UpperTheory.PushoutCovers

open UpperTheory.PushoutCovers in
theorem UpperTheory.doubleMappingCylinder_cochain_extension :
    ∀ (R : Type) [CommRing R] (P : Arrow Spc), (∀ (p : ℕ) (U : Scheme.{0}) (w : Sx (dbl P) p U), (∃ z : Sx P.right p U, z.map (dbl.inl P) = w) ∨ ∃ z : Sx P.right p U, z.map (dbl.inr P) = w) ∧
    ∀ (K : Cx R) (m N : ℤ) (x : (famDC (Sub.img P.hom) K m).Tot),
      ∃ γ : Cochain ((chains R).obj (dbl P)) K N, Comp (dbl.inl P) γ x ∧
        ∀ (p : ℕ) (s : ℤ) h (U : Scheme.{0}) (z : Sx P.right p U),
          ev (R := R) γ p s h U (z.map (dbl.inr P)) = 0 := by
  intro R _ P
  refine ⟨fun p U w => cover P p U w, ?_⟩
  intro K m N x
  have key : ∀ (p : ℕ) (s' : ℤ) (U : Scheme.{0}), ∃ φ : Sx (dbl P) p U → Sec (K.X s') U,
      ∀ (s : ℤ) (e : s + m = s'), ∀ z : Sx P.right p U,
        φ (z.map (dbl.inl P)) = e ▸ (x p s).1 U z ∧ φ (z.map (dbl.inr P)) = 0 := by
    intro p s' U
    obtain ⟨s, rfl⟩ : ∃ s, s' = s + m := ⟨s' - m, by ring⟩
    obtain ⟨φ, h1, h2⟩ := fn P p U (T := Sec (K.X (s + m)) U) ((x p s).1 U)
      (fun y => (x p s).2.2 U _ ⟨y, rfl⟩)
    refine ⟨φ, fun s1 e z => ?_⟩
    obtain rfl : s1 = s := by omega
    exact ⟨h1 z, h2 z⟩
  choose φ hφ using key
  have nat : ∀ (p : ℕ) (s' : ℤ) (_ : -(p : ℤ) + N = s') (V U : Scheme.{0}) (g : V ⟶ U)
      (w : Sx (dbl P) p U), Sec.res g (φ p s' U w) = φ p s' V (Sx.res g w) := by
    intro p s' _ V U g w
    obtain ⟨s, rfl⟩ : ∃ s, s' = s + m := ⟨s' - m, by ring⟩
    rcases cover P p U w with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · rw [(hφ p (s + m) U s rfl z).1, res_map, (hφ p (s + m) V s rfl _).1]
      exact (x p s).2.1 V U g z
    · rw [(hφ p (s + m) U s rfl z).2, res_map, (hφ p (s + m) V s rfl _).2]
      exact map_zero _
  have components : ∀ (i j : ℤ) (hij : i + N = j), ∃ ψ : ((chains R).obj (dbl P)).X i ⟶ K.X j,
      ∀ (p : ℕ) (hp : i = -(p : ℤ)) U z,
        Sec.map ((chainsXIso R (dbl P) p).inv ≫ eqToHom (congrArg ((chains R).obj (dbl P)).X hp.symm) ≫ ψ)
          (freeGen R _ U z) = φ p j U z := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨ψ, hψ⟩ := CupSpec.free_exists (R := R) _ _ (φ k j) (nat k j hij)
      refine ⟨(chainsXIso R (dbl P) k).hom ≫ ψ, fun p hp U z => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hψ U z
    · exact ⟨0, fun p hp => by omega⟩
  choose ψ hψ using components
  let γ : Cochain ((chains R).obj (dbl P)) K N := Cochain.mk ψ
  have hγ : ∀ p s h U z, ev γ p s h U z = φ p s U z := by
    intro p s h U z
    have he := hψ _ _ h p rfl U z
    rw [eqToHom_refl, Category.id_comp] at he
    exact he
  refine ⟨γ, fun p s h U z => ?_, fun p s h U z => ?_⟩
  · rw [hγ]
    exact ((hφ p (s + m) U s rfl z).1).symm
  · rw [hγ]
    exact (hφ p s U (s - m) (by ring) z).2
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_subalgebra_eq_range_germToFunctionField :
    ∀ (k : Type) [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k) [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], ∃ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) := by
  intro k _ C _ c _ h W _
  have hη : genericPoint C ∈ (⊤ : C.Opens) := trivial
  have key : CommRingCat.ofHom (algebraMap k C.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) hη := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).hom, ← Scheme.ΓSpecIso_naturality, h]
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Iso.hom_inv_id_assoc]
    congr 1
    rw [Scheme.fromSpecStalk_appTop]
    have e1 : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [e1, op_id, CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]
    exact congrArg (C.presheaf.germ ⊤ (genericPoint C) _ ≫ ·) (Iso.inv_hom_id _) |>.trans
      (Category.comp_id _)
  refine ⟨{ (C.germToFunctionField W).hom.range with algebraMap_mem' := ?_ }, ?_⟩
  · intro r
    refine ⟨C.presheaf.map (homOfLE le_top).op (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)), ?_⟩
    have hr := congrArg (fun f => f.hom r) key
    simp only [CommRingCat.hom_ofHom, CommRingCat.comp_apply] at hr
    rw [hr]
    exact C.presheaf.germ_res_apply (homOfLE le_top) _ _ _
  · rfl
end
