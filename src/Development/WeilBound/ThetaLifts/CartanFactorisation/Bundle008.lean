module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle006
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle007
import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle004
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle005
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle003
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem ker_of_eq {Q P P₂ : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup P] [Module ℂ P] [AddCommGroup P₂] [Module ℂ P₂]
    {S : Submodule ℂ Q} {p : Q →ₗ[ℂ] P} {p₂ : Q →ₗ[ℂ] P₂} (h : LinearMap.ker p ⊓ S = LinearMap.ker p₂ ⊓ S) :
    ∀ x ∈ S, p x = 0 ↔ p₂ x = 0 := fun x hx =>
  ⟨fun h0 => (h ▸ (⟨h0, hx⟩ : x ∈ LinearMap.ker p ⊓ S) : x ∈ LinearMap.ker p₂ ⊓ S).1,
    fun h0 => (h.symm ▸ (⟨h0, hx⟩ : x ∈ LinearMap.ker p₂ ⊓ S) : x ∈ LinearMap.ker p ⊓ S).1⟩

theorem max_uniq {α : Type} [SemilatticeSup α] {St : α → Prop} {S N N' : α} (hs : St (N ⊔ N'))
    (h : N ≠ S → N' ≠ S → N ⊔ N' ≠ S) (h1 : Maximal (fun P => St P ∧ P ≠ S) N) (h2 : Maximal (fun P => St P ∧ P ≠ S) N') :
    N = N' :=
  le_antisymm (le_sup_left.trans (h2.2 ⟨hs, h h1.1.2 h2.1.2⟩ le_sup_right)) (le_sup_right.trans (h1.2 ⟨hs, h h1.1.2 h2.1.2⟩ le_sup_left))

theorem real_trans (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) {R : RealMaps F a a'} {V V' W} (t : IsTriple B G X om om')
    (t₂ : IsTriple B (reG G V V' W) X om om') (r : IsRealMaps B G om om' R) {g g' h T T'} (hg : Moves B G.V V g)
    (hg' : Moves B G.V' V' g') (hh : Moves B G.W W h) (hT : IsArchOp om (g, h) T) (hT' : IsArchOp om' (g', h) T')
    (hP : ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = G.M.Pol B.ψ B.emb)
    (hP' : ((reG G V V' W).M'.Pol B.ψ B.emb).map (T' : _ →ₗ[ℂ] _) = G.M'.Pol B.ψ B.emb) :
    IsRealMaps B (reG G V V' W) om om' ⟨R.Pi, R.p ∘ₗ (T : _ →ₗ[ℂ] _), R.p' ∘ₗ (T' : _ →ₗ[ℂ] _)⟩ := by
  have hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
    ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩
  have res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {m n k : ℕ} (h : ResEtaPow K χ m)
      (h' : ResEtaPow K χ' n) (e : k = m + n) : ResEtaPow K (χ / χ') k := fun x => by
    rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]
  have pairV {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
      IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, hecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
      res_div h.chars.resβ h.chars.resα rfl, h.weil⟩
  have pairV' {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
      IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, hecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
      res_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩
  have quot_trans {n d : ℕ} {Y Y₂ : Spc F E n} {Z Z₂ : Spc F E d}
      {M : Model σ Y Z} {M₂ : Model σ (reS Y Y₂) (reS Z Z₂)}
      {χY χZ : Chr F E} {o : Rep σ Y Z} {u v u' v' : ℕ}
      (hp : IsPair B M χY χZ o u v u' v') (hp₂ : IsPair B M₂ χY χZ o u v u' v')
      {g h T} (hg : Moves B Y Y₂ g) (hT : IsArchOp o (g, h) T)
      (hP : (M₂.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = M.Pol B.ψ B.emb)
      {P : Type} [AddCommGroup P] [Module ℂ P] {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P}
      (q : RealQuot B M o p) : RealQuot B M₂ o (p ∘ₗ (T : _ →ₗ[ℂ] _)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Submodule.map_comp, hP, q.onto]
    · exact fun γ hγ f hf f₁ ha => q.lie _ (conj_line hg.1 hγ) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T f₁)
        (transL hO hL hQ hp hp₂ hT hP (conj_line hg.1 hγ) one_line hγ one_line (fun t => cj1 g (γ t) h) hf ha)
    · exact fun k hk f hf f₁ ha => q.cpt _ (hg.up hk) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T f₁)
        (transK hO hQ hp hT (hg.up hk).1 (one_at _) (cj1 g k h) ha)
  have p1 := pairV t
  have p2 := pairV' t
  have q1 := pairV t₂
  have q2 := pairV' t₂
  refine ⟨quot_trans p1 q1 hg hT hP r.quot, quot_trans p2 q2 hg' hT' hP' r.quot',
    fun γ hγ f hf f' hf' f₁ f₁' a1 a2 => r.lie _ (conj_line hh.1 hγ) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T' f') (hP' ▸ ⟨f', hf', rfl⟩) _ _
      (transL hO hL hQ p1 q1 hT hP one_line (conj_line hh.1 hγ) one_line hγ (fun t => cj2 g h (γ t)) hf a1)
      (transL hO hL hQ p2 q2 hT' hP' one_line (conj_line hh.1 hγ) one_line hγ (fun t => cj2 g' h (γ t)) hf' a2),
    fun k hk f hf f' hf' f₁ f₁' a1 a2 => r.cpt _ (hh.up hk) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T' f') (hP' ▸ ⟨f', hf', rfl⟩) _ _
      (transK hO hQ p1 hT (one_at _) (hh.up hk).1 (cj2 g h k) a1) (transK hO hQ p2 hT' (one_at _) (hh.up hk).1 (cj2 g' h k) a2),
    r.nontriv, fun N h1 h2 => r.irred N (fun γ hγ f hf y e hp => ?_) fun k hk f hf y e hp => ?_⟩
  · obtain ⟨u, hu, rfl⟩ : f ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) := hP ▸ hf
    have l := conj_line (re_inv hh.1) hγ
    obtain ⟨z, -, hz⟩ := pol_lie hO hL hQ q1 one_line l hu
    have := transL hO hL hQ p1 q1 hT hP one_line hγ one_line l (fun t => cj3 g h (γ t)) hu ((hz z).2 rfl)
    rw [(hQ F _ _ y (T z)).2 _ e this]
    exact h1 _ l u hu z ((hz z).2 rfl) hp
  · obtain ⟨u, hu, rfl⟩ : f ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) := hP ▸ hf
    have l := hh.down hk
    obtain ⟨z, -, hz⟩ := pol_k hO hQ q1 (one_kinf _) l hu
    have := transK hO hQ p1 hT (one_at _) hk.1 (cj3 g h k) ((hz z).2 rfl)
    rw [(hQ F _ _ y (T z)).1 _ e this]
    exact h2 _ l u hu z ((hz z).2 rfl) hp

theorem I_move (hI : ILeft) {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χ χ' : Chr F E} {o : Rep σ Y W}
    {r s r' s' : ℕ} (hp : IsPair B M χ χ' o r s r' s') {Φ} (hΦ : Φ ∈ schA F _) (g h x) :
    M.I o (o (g, h) Φ) x = M.I o Φ (x * h) := by
  rw [show (g, h) = ((g, 1) : UA σ Y.J × UA σ W.J) * (1, h) by simp, map_mul, Module.End.mul_apply,
    hI F E σ B n d Y W M χ χ' o r s r' s' hp _ (hp.weil.isUSplitting.pres _ _ hΦ), I_right]

theorem move_sum {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ} (hM : M.IsGood ψ) {o : Rep σ Y W} {x T}
    (hT : IsArchOp o x T) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h1 : ∀ i v, φ i v ∈ SB _) (h2 : ∀ i, ∀ᶠ v in cofinite, φ i v = M.vac v) :
    o x (∑ i, pure (f i) (φ i)) = ∑ i, pure (T (f i)) (φ i) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨g, hg, e⟩ := pure_eq_pureA hM (φ i) (h1 i) (h2 i)
  rw [e, e, hT.1 _ g hg]

theorem so_re (V V' W) : G.M'.So B.ψ B.τ₁ ≤ (reG G V V' W).M'.So B.ψ B.τ₁ := by
  refine Submodule.span_mono ?_
  rintro _ ⟨f, φ, h1, h2, ⟨h3, ι, h4, h5⟩, rfl⟩
  exact ⟨f, φ, h1, h2, ⟨h3, ι, ⟨h4.bij, h4.trans, h4.mult⟩, h5⟩, rfl⟩

end PositivityTheory.ThKF

end
end

section

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG
open scoped Classical

theorem exists_enlarge {α : Type} {Q : α → Type} [∀ v, AddCommGroup (Q v)] [∀ v, Module ℂ (Q v)] (z : ∀ v, Q v)
    {T T' : Finset α} (h : T ⊆ T') : ∃ L : PiTensorProduct ℂ (fun v : T => Q v) →ₗ[ℂ] PiTensorProduct ℂ (fun v : T' => Q v),
      ∀ y : ∀ v, Q v, (∀ v ∉ T, y v = z v) →
        L (PiTensorProduct.tprod ℂ fun v : T => y v) = PiTensorProduct.tprod ℂ fun v : T' => y v := by
  let e : (∀ v : T, Q v) → ∀ v : T', Q v := fun ψ v => if hv : v.1 ∈ T then ψ ⟨v, hv⟩ else z v
  have he : ∀ [DecidableEq T] (ψ : ∀ v : T, Q v) (i : T) (x : Q i),
      e (Function.update ψ i x) = Function.update (e ψ) ⟨i.1, h i.2⟩ x := by
    intro _ ψ i x
    funext v
    by_cases hv : v = ⟨i.1, h i.2⟩
    · subst hv; simp only [e, dif_pos i.2, Function.update_self]
    · rw [Function.update_of_ne hv]
      simp only [e]
      split_ifs with hT
      · exact Function.update_of_ne (f := ψ) (a := ⟨v.1, hT⟩) (a' := i) (fun k => hv (Subtype.ext (congrArg Subtype.val k :))) _
      · rfl
  refine ⟨PiTensorProduct.lift
    { toFun := fun ψ => PiTensorProduct.tprod ℂ (e ψ)
      map_update_add' := fun ψ i x y => by rw [he, he, he, MultilinearMap.map_update_add]
      map_update_smul' := fun ψ i c x => by rw [he, he, MultilinearMap.map_update_smul] }, fun y hy => ?_⟩
  rw [PiTensorProduct.lift.tprod]
  change PiTensorProduct.tprod ℂ (e fun v => y v) = _
  congr 1
  funext v
  simp only [e]
  split_ifs with hv
  exacts [rfl, (hy v hv).symm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem kill_aug (hI : ILeft) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
    (hp : IsPair B M χX χW om r s r' s') (J : Fn F n d →ₗ[ℂ] (UA σ W.J → ℂ)) (hJ : ∀ Φ ∈ schA F _, J Φ = M.I om Φ)
    (v : Pl F) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (h1 : ∀ v, φ v ∈ SB _) (h2 : Std φ)
    (z : (Fin n × Fin d → Fv F v) → ℂ) (hz : z ∈ augAt om v) : J (pure f (Function.update φ v z)) = 0 := by
  obtain ⟨ρ, hρ, hρ'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ h2
  let t : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Fn F n d :=
    { toFun := fun z => tens (evFin F v) z ρ
      map_add' := fun x y => funext fun _ => add_mul _ _ _
      map_smul' := fun a x => funext fun _ => mul_assoc _ _ _ }
  have mem : ∀ y ∈ SB _, t y ∈ schA F _ := fun y hy => by
    change tens (evFin F v) y ρ ∈ _
    rw [hρ']
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun u => ?_) (GlobalTheory.PureFactor.update_eventually φ v y h2)
    by_cases hu : u = v
    · subst hu; rw [Function.update_self]; exact hy
    · rw [Function.update_of_ne hu]; exact h1 u
  rw [← hρ']
  change (J ∘ₗ t) z = 0
  refine (Submodule.span_le.2 ?_ : augAt om v ≤ LinearMap.ker (J ∘ₗ t)) hz
  rintro _ ⟨g, -, y, hy, y₁, hy₁, ha, rfl⟩
  have e : om (g, 1) (t y) = t y₁ := ha ρ ⟨hρ, mem y hy⟩
  change J (t (y₁ - y)) = 0
  rw [map_sub, map_sub, hJ _ (mem y₁ hy₁), hJ _ (mem y hy), ← e, hI F E σ B n d X W M χX χW om r s r' s' hp _ (mem y hy), sub_self]

theorem anAll_of (hW : WeilConv) (hC : KCoinv) (hI : ILeft) : AnAll := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm hq c hc Φ Φ' ⟨T, hT, m, m', f, φ, f', φ', h1, h2, e1, e2, e⟩ h
  have g := hm.triple.geo.hM
  have g' := hm.triple.geo.hM'
  have hp : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
      (a + a' - (G.p + G.q)) (G.p + G.q) := by
    have hd : IsHecke F E (X.α / X.β) :=
      ⟨hm.triple.chars.heckeα.1.div' hm.triple.chars.heckeβ.1, fun x => by
        rw [MonoidHom.div_apply, hm.triple.chars.heckeα.2, hm.triple.chars.heckeβ.2, div_one]⟩
    have hr : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (X.α / X.β) (a + a') := by
      intro x
      rw [MonoidHom.div_apply, Circle.coe_div, hm.triple.chars.resα, hm.triple.chars.resβ, add_comm a a']
      split_ifs
      · simp
      · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]
    exact ⟨hm.triple.base, hm.triple.geo.hV', hm.triple.geo.hW, g',
      hm.triple.chars.heckeα, hd, hm.triple.chars.resα, hr, hm.triple.weil'⟩
  obtain ⟨J, hJ⟩ := exists_Ilin hm.triple.weil' (schA F _) le_rfl fun Φ hΦ =>
    ((hW F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hp (Or.inr (by rw [hq]; simp))).1 Φ hΦ).1
  obtain ⟨-, c2, c3, -⟩ := (hC F E σ B a a' G X om om' R Rf hm).1 B.v₁ hm.triple.chars.good
  choose y hy hy' using fun j => c3 B.τ₁ (Rf.p' B.v₁ (φ' j B.v₁))
  let φ₀ : Fin m' → ∀ v : Pl F, _ := fun j => Function.update (φ' j) B.v₁ (y j)
  have sb : ∀ j v, φ₀ j v ∈ SB _ := fun j v => by
    by_cases hv : v = B.v₁
    · subst hv; simp only [φ₀, Function.update_self]; exact (hy j).1
    · simp only [φ₀, Function.update_of_ne hv]; exact (h2 j).2.1 v
  have off : ∀ j, ∀ v ∉ insert B.v₁ T, φ₀ j v = G.M'.vac v := fun j v hv => by
    rw [Finset.mem_insert, not_or] at hv
    simp only [φ₀, Function.update_of_ne hv.1]; exact (h2 j).2.2 v hv.2
  have pe : ∀ j v, Rf.p' v (φ₀ j v) = Rf.p' v (φ' j v) := fun j v => by
    by_cases hv : v = B.v₁
    · subst hv; simp only [φ₀, Function.update_self]; exact hy' j
    · simp only [φ₀, Function.update_of_ne hv]
  have so : ∑ j, pure (f' j) (φ₀ j) ∈ G.M'.So B.ψ B.τ₁ := sum_mem fun j _ =>
    pure_mem_So g' _ _ _ (fun v _ => sb j v) (ev_of_off (off j))
      (by simp only [φ₀, Function.update_self]; exact Submodule.subset_span (hy j))
  obtain ⟨L, hL⟩ := exists_enlarge (fun v => Rf.p v (G.M.vac v)) (Finset.subset_insert B.v₁ T)
  have pm : PolMatch B G X R Rf Φ (∑ j, pure (f' j) (φ₀ j)) := by
    refine ⟨insert B.v₁ T, hT.trans (Finset.subset_insert _ _), m, m', f, φ, f', φ₀,
      fun i => ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v fun k => hv (Finset.mem_insert_of_mem k)⟩,
      fun j => ⟨(h2 j).1, sb j, off j⟩, e1, rfl, ?_⟩
    have := congrArg (TensorProduct.map LinearMap.id L) e

    simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply] at this
    simp only [pe]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [hL (fun v => Rf.p v (φ i v)) fun v hv => by rw [(h1 i).2.2 v hv]]
    · rw [hL (fun v => Rf.p' v (φ' j v)) fun v hv => by
        rw [(h2 j).2.2 v hv, (hm.fin.sph v fun k => hv (hT k)).1]]
  rw [hc Φ _ so pm h]
  congr 1
  have st : ∀ j, Std (φ' j) := fun j => (good_std g').congr (ev_of_off (h2 j).2.2)
  have m1 : Φ' ∈ schA F _ := e2 ▸ sum_mem fun j _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (h2 j).2.1 (st j)

  rw [← hJ _ (so_le g' _ so), ← hJ _ m1, e2, map_sum, map_sum]
  refine congrFun (Finset.sum_congr rfl fun j _ => ?_) h
  have k := kill_aug hI hp J hJ B.v₁ (f' j) (φ' j) (h2 j).2.1 (st j) (y j - φ' j B.v₁)
    ((c2 _ (sub_mem (hy j).1 ((h2 j).2.1 _))).1 (by rw [map_sub, hy', sub_self]))
  have a2 := (pureAct F _ B.v₁ id (f' j) (φ' j) (h2 j).2.1 (st j)).2.1 (φ' j B.v₁) (y j - φ' j B.v₁) 1
  rw [one_smul, one_smul, add_sub_cancel, Function.update_eq_self] at a2
  have k' : J (pure (f' j) (φ₀ j)) = J (pure (f' j) (φ' j)) := by
    have := congrArg J a2
    rw [map_add (f := _)] at this
    exact this.trans (by rw [show J _ = 0 from k, add_zero])
  exact k'

end PositivityTheory.ThKF

end
end

section

noncomputable section

namespace PositivityTheory.ThKF

open GlobalTheory.ThK

theorem iLeft (hT : ThetaBasic) : ILeft := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp _ hΦ g =>
  I_left unimodularity_holds hT hp hΦ g

end PositivityTheory.ThKF

end
end
