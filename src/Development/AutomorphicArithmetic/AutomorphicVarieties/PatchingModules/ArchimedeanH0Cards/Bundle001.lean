module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.PushforwardPreservesSelmerCocycles
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

section

variable {k G M : Type} [CommRing k] [Group G] [AddCommGroup M] [Module k M]

end

private theorem dn_two_apply' {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (rho : Representation R G M) (F : (Fin 2 → G) → M) (g : Fin 3 → G) :
    dn rho 2 F g = rho (g 0) (F ![g 1, g 2]) - F ![g 0 * g 1, g 2] + F ![g 0, g 1 * g 2] - F ![g 0, g 1] := by
  have e0 : (fun i : Fin 2 => g i.succ) = ![g 1, g 2] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (fun x y : G => x * y) g = ![g 0 * g 1, g 2] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e2 : Fin.contractNth 1 (fun x y : G => x * y) g = ![g 0, g 1 * g 2] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e3 : Fin.contractNth 2 (fun x y : G => x * y) g = ![g 0, g 1] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  simp only [dn, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_succ, Fin.sum_univ_zero, e0, e1]
  norm_num
  rw [e2, e3]
  abel

private theorem dn_three_apply {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (rho : Representation R G M) (F : (Fin 3 → G) → M) (g : Fin 4 → G) :
    dn rho 3 F g = rho (g 0) (F ![g 1, g 2, g 3]) - F ![g 0 * g 1, g 2, g 3] + F ![g 0, g 1 * g 2, g 3]
      - F ![g 0, g 1, g 2 * g 3] + F ![g 0, g 1, g 2] := by
  have e0 : (fun i : Fin 3 => g i.succ) = ![g 1, g 2, g 3] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (fun x y : G => x * y) g = ![g 0 * g 1, g 2, g 3] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e2 : Fin.contractNth 1 (fun x y : G => x * y) g = ![g 0, g 1 * g 2, g 3] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e3 : Fin.contractNth 2 (fun x y : G => x * y) g = ![g 0, g 1, g 2 * g 3] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e4 : Fin.contractNth 3 (fun x y : G => x * y) g = ![g 0, g 1, g 2] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  simp only [dn, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_succ, Fin.sum_univ_zero, e0, e1]
  norm_num
  rw [e2, e3, e4]
  abel

theorem UpperTheory.V.Pa.B2.H2_right_exact_mod_l_of_H3_subsingleton :
    ∀ (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], (∀ (A : Type) [CommRing A] (M : FRep A G), (∀ m : M.X, l • m = 0) → Subsingleton (Hn M.ρ 3)) → SecondCohomologyRightExactModL l G := by
  intro l G _ _ _ h A _ M M' hl u hu hs
  intro x
  obtain ⟨c', rfl⟩ := Submodule.Quotient.mk_surjective _ x
  set s := Function.surjInv hs with hs_def
  have us : ∀ y, u (s y) = y := Function.surjInv_eq hs
  let c : G × G → M.X := fun p => s (c'.1 p)
  have hc : Continuous c := (continuous_of_discreteTopology (f := s)).comp c'.2.1
  let N : Submodule A M.X := LinearMap.ker u
  have hN : ∀ g : G, ∀ m ∈ N, M.ρ g m ∈ N := by
    intro g m hm
    simp only [N, LinearMap.mem_ker] at hm ⊢
    rw [hu, hm, map_zero]
  let ρK : Representation A G N :=
    { toFun := fun g => (M.ρ g).restrict (hN g)
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro g g'
        ext m
        simp }
  have hcont : ContAction ρK :=
    continuous_induced_rng.2 (M.cont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  let K : FRep A G := FRep.mk N ρK hcont
  have hKl : ∀ m : K.X, l • m = 0 := by
    intro m
    exact Subtype.ext (hl m.1)
  have hsub := h A K hKl
  let C : (Fin 2 → G) → M.X := fun x => c (x 0, x 1)
  have hfN : ∀ g : Fin 3 → G, dn M.ρ 2 C g ∈ N := by
    intro g
    simp only [N, LinearMap.mem_ker]
    rw [dn_two_apply']
    simp only [C, c, map_sub, map_add (f := _), hu, us]
    simpa using c'.2.2 (g 0) (g 1) (g 2)
  let f : (Fin 3 → G) → N := fun g => ⟨dn M.ρ 2 C g, hfN g⟩
  have key : ∀ t : Fin 3 → G, ((f t : N) : M.X) =
      M.ρ (t 0) (c (t 1, t 2)) - c (t 0 * t 1, t 2) + c (t 0, t 1 * t 2) - c (t 0, t 1) := by
    intro t
    simp [f, dn_two_apply', C]
  have hρK : ∀ (a : G) (m : N), ((ρK a m : N) : M.X) = M.ρ a m := fun a m => rfl
  have hmul : ∀ (a b : G) (m : M.X), M.ρ a (M.ρ b m) = M.ρ (a * b) m := by
    intro a b m
    simp [map_mul]
  have fcont : Continuous f := by
    apply continuous_induced_rng.2
    have e : (Subtype.val ∘ f) = fun t : Fin 3 → G =>
        M.ρ (t 0) (c (t 1, t 2)) - c (t 0 * t 1, t 2) + c (t 0, t 1 * t 2) - c (t 0, t 1) := funext key
    rw [e]
    have c0 := continuous_apply (A := fun _ : Fin 3 => G) 0
    have c1 := continuous_apply (A := fun _ : Fin 3 => G) 1
    have c2 := continuous_apply (A := fun _ : Fin 3 => G) 2
    exact (((M.cont.comp (c0.prodMk (hc.comp (c1.prodMk c2)))).sub
      (hc.comp ((c0.mul c1).prodMk c2))).add (hc.comp (c0.prodMk (c1.mul c2)))).sub
      (hc.comp (c0.prodMk c1))
  have fcyc : dn ρK 3 f = 0 := by
    funext g
    apply Subtype.ext
    rw [dn_three_apply]
    simp only [Submodule.coe_add, Submodule.coe_sub, hρK, key, Pi.zero_apply, ZeroMemClass.coe_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_sub, map_add, hmul]
    simp only [mul_assoc]
    abel
  have fmem : f ∈ Zn K.ρ 3 := by
    refine Submodule.mem_inf.2 ⟨fcont, ?_⟩
    exact LinearMap.mem_ker.2 fcyc
  have h0 : (Submodule.Quotient.mk ⟨f, fmem⟩ : Hn K.ρ 3) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h0
  change f ∈ Submodule.map (dn ρK 2) (Cn ρK 2) at h0
  obtain ⟨b, hb, hbf⟩ := h0
  have hbc : Continuous b := hb
  have hv : Continuous fun p : G × G => ![p.1, p.2] := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  let c2 : G × G → M.X := fun p => c p - (b ![p.1, p.2] : M.X)
  have hc2 : c2 ∈ Z2 M.ρ := by
    refine ⟨hc.sub (continuous_subtype_val.comp (hbc.comp hv)), ?_⟩
    intro g g' g''
    have e := congrArg Subtype.val (congrFun hbf ![g, g', g''])
    rw [dn_two_apply'] at e
    simp only [Submodule.coe_add, Submodule.coe_sub, hρK, key, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e
    simp only [c2, map_sub]
    calc _ = (M.ρ g (c (g', g'')) - c (g * g', g'') + c (g, g' * g'') - c (g, g'))
          - (M.ρ g (b ![g', g''] : M.X) - (b ![g * g', g''] : M.X) + (b ![g, g' * g''] : M.X)
            - (b ![g, g'] : M.X)) := by abel
      _ = 0 := by rw [e, sub_self]
  refine ⟨Submodule.Quotient.mk ⟨c2, hc2⟩, ?_⟩
  simp only [mapH2, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  funext p
  show u (c2 p) = c'.1 p
  simp only [c2, c, map_sub, us, LinearMap.mem_ker.1 (b _).2, sub_zero]
end

section

open ReciprocityTheory.Gal

namespace UpperTheory.V.Pa.B2

variable {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem continuous_differential_one (M : FRep A Γ) {x : Γ → M.X} (hx : Continuous x) : Continuous (d1 M.ρ x) :=
  ((M.cont.comp (continuous_fst.prodMk (hx.comp continuous_snd))).sub (hx.comp continuous_mul)).add
    (hx.comp continuous_fst)

theorem urLift {l : ℕ} {J : Subgroup Γ} (H : UrAx l J) (M : FRep A Γ) (hl : ∀ m : M.X, l • m = 0)
    (hJ : ∀ g ∈ J, ∀ m, M.ρ g m = m) (S : Submodule A M.X) (hS : ∀ g, S ≤ S.comap (M.ρ g)) (x : Γ → M.X)
    (hx : Continuous x) (hd : ∀ s, d1 M.ρ x s ∈ S) (h0 : ∀ g ∈ J, x g ∈ S) :
    ∃ b ∈ Z1 M.ρ, (∀ g ∈ J, b g = 0) ∧ ∀ g, x g - b g ∈ S := by
  letI : TopologicalSpace (M.X ⧸ S) := ⊥
  haveI : DiscreteTopology (M.X ⧸ S) := ⟨rfl⟩
  haveI : Finite (M.X ⧸ S) := Finite.of_surjective _ S.mkQ_surjective
  let M' : FRep A Γ :=
    { X := M.X ⧸ S
      ρ := Representation.quotient M.ρ S hS
      cont := by
        refine continuous_prod_of_discrete_right.2 fun q => ?_
        obtain ⟨m, rfl⟩ := S.mkQ_surjective q
        exact (continuous_of_discreteTopology (f := S.mkQ)).comp
          (M.cont.comp (continuous_id.prodMk continuous_const)) }
  obtain ⟨b, hb, h1, h2⟩ := (H A M hl hJ).2 M' S.mkQ (fun _ _ => rfl) S.mkQ_surjective (fun g => S.mkQ (x g))
    ⟨(continuous_of_discreteTopology (f := S.mkQ)).comp hx, fun g h => by
      show S.mkQ (x (g * h)) = S.mkQ (x g) + S.mkQ (M.ρ g (x h))
      rw [← map_add (f := _)]
      refine (Submodule.Quotient.eq S).2 ?_
      convert S.neg_mem (hd (g, h)) using 1
      rw [d1_apply]; abel⟩
    (fun g hg => (Submodule.Quotient.mk_eq_zero S).2 (h0 g hg))
  exact ⟨b, hb, h1, fun g => (Submodule.Quotient.eq S).1 (h2 g).symm⟩

theorem translGen {P : Pl Γ} (D : Dat A P) (M : FRep A Γ) (ι : D.M.X →ₗ[A] M.X) (hi : Function.Injective ι)
    (he : ∀ g m, ι (D.M.ρ g m) = M.ρ g (ι m)) (N : P.ι → Submodule A M.X)
    (hN : ∀ w g, ∀ m ∈ N w, M.ρ (P.φ w g) m ∈ N w) (hk : ∀ w m, D.π w m = 0 ↔ ι m ∈ N w) (c0 : Γ)
    (hc : c0 * c0 = 1) (h2 : IsUnit (2 : A)) {e : ℕ} (x : Fin e → Γ → M.X) (hx : ∀ i, Continuous (x i))
    (hd : ∀ i s, d1 M.ρ (x i) s ∈ LinearMap.range ι) (hxc : ∀ i, x i c0 ∈ LinearMap.range ι)
    (b : Fin e → ∀ w, P.G w → M.X) (hb : ∀ i w, Continuous (b i w))
    (hb' : ∀ i w g h, b i w (g * h) = b i w g + M.ρ (P.φ w g) (b i w h))
    (hxb : ∀ i w g, ∃ m, x i (P.φ w g) - b i w g - ι m ∈ N w) :
    ∃ ξ : Fin e → D.selmerSecondCocycles, ∀ c : Fin e → A, ((∑ i, c i • ξ i : D.selmerSecondCocycles) : D.C2) ∈ D.selmerSecondCoboundaries →
      ∃ Ψ ∈ Z1 M.ρ, Ψ c0 = 0 ∧ (∀ γ, Ψ γ - ∑ i, c i • x i γ ∈ LinearMap.range ι) ∧
        ∀ w, ∃ m, ∀ g ∈ P.J w, Ψ (P.φ w g) - ∑ i, c i • b i w g - (M.ρ (P.φ w g) (ι m) - ι m) ∈ N w := by
  classical
  obtain ⟨r, hr⟩ := hi.hasLeftInverse
  have hr' : ∀ i s, ι (r (d1 M.ρ (x i) s)) = d1 M.ρ (x i) s := fun i s => by
    obtain ⟨m, hm⟩ := hd i s
    rw [← hm, hr]
  let σ : P.ι → M.X → D.M.X := fun w s => Classical.epsilon fun m => s - ι m ∈ N w
  let τ : Fin e → ∀ w, P.G w → D.M.X := fun i w g => σ w (x i (P.φ w g) - b i w g)
  have hτ : ∀ i w g, x i (P.φ w g) - b i w g - ι (τ i w g) ∈ N w := fun i w g =>
    Classical.epsilon_spec (hxb i w g)
  have mem : ∀ i, ((fun s => r (d1 M.ρ (x i) s), fun w g => D.π w (τ i w g)) : D.C2) ∈ D.selmerSecondCocycles := by
    intro i
    refine ⟨⟨(continuous_of_discreteTopology (f := r)).comp (continuous_differential_one M (hx i)), fun g h k => hi ?_⟩,
      fun w => ⟨?_, fun g h => ?_⟩⟩
    · simp only [map_add (f := _), map_sub, map_zero, he, hr']
      simp only [d1_apply, map_add (f := _), map_sub, map_mul, mul_apply_eq_comp, mul_assoc]
      abel
    · exact (continuous_of_discreteTopology (f := fun s => D.π w (σ w s))).comp
        (((hx i).comp (P.cont w)).sub (hb i w))
    · simp only [d1_apply (D.Q w).ρ, ← D.equiv]
      rw [← map_sub, ← map_add (f := _), ← sub_eq_zero, ← map_sub, hk]
      simp only [map_add (f := _), map_sub, he, hr']
      convert add_mem (sub_mem (hN w g _ (hτ i w h)) (hτ i w (g * h))) (hτ i w g) using 1
      simp only [d1_apply, map_add (f := _), map_sub, map_mul, hb']
      abel
  refine ⟨fun i => ⟨_, mem i⟩, fun c hB => ?_⟩
  obtain ⟨x0, c1, e1, e2⟩ := hB
  have e1' : ∀ s, ∑ i, c i • d1 M.ρ (x i) s = ι (d1 D.M.ρ x0 s) := fun s => by
    rw [← e1]
    simp [Prod.fst_sum, Finset.sum_apply, hr']
  have hΨ : (fun γ => ∑ i, c i • x i γ - ι (x0 γ)) ∈ Z1 M.ρ := by
    refine ⟨(continuous_finsetSum _ fun i _ => (hx i).const_smul _).sub
      ((continuous_of_discreteTopology (f := ι)).comp c1), fun g h => ?_⟩
    have := e1' (g, h)
    simp only [d1_apply, map_add (f := _), map_sub, he, smul_add, smul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib] at this

    simp only [map_sub, map_sum, map_smul]
    rw [← sub_eq_zero] at this ⊢
    rw [← neg_eq_zero, ← this]
    abel
  obtain ⟨m0, hm0⟩ : ∑ i, c i • x i c0 - ι (x0 c0) ∈ LinearMap.range ι :=
    sub_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxc i)) ⟨_, rfl⟩
  have hneg : M.ρ c0 (ι m0) = -ι m0 := by
    have a1 := hΨ.2 1 1
    have a2 := hΨ.2 c0 c0
    simp only [mul_one, map_one, one_apply_eq_self, left_eq_add] at a1
    simp only [hc, a1, ← hm0] at a2
    exact eq_neg_of_add_eq_zero_right a2.symm
  obtain ⟨t, ht⟩ := h2.exists_left_inv
  refine ⟨(fun γ => ∑ i, c i • x i γ - ι (x0 γ)) + d0 M.ρ (ι (t • m0)), add_mem hΨ ⟨?_, fun g h => ?_⟩, ?_,
    fun γ => ?_, fun w => ?_⟩
  · exact (M.cont.comp (continuous_id.prodMk continuous_const)).sub continuous_const
  · simp only [amitsur_d0_apply, map_mul, map_sub, mul_apply_eq_comp]; abel
  · simp only [Pi.add_apply, amitsur_d0_apply, ← hm0]
    rw [map_smul, map_smul, hneg, ← smul_sub, ← neg_add', ← two_smul A, smul_neg, smul_smul, ht, one_smul, add_neg_cancel]
  · refine ⟨D.M.ρ γ (t • m0) - t • m0 - x0 γ, ?_⟩
    simp only [Pi.add_apply, amitsur_d0_apply, map_sub, he]
    abel
  · obtain ⟨-, Y, hY⟩ := e2 w
    obtain ⟨m, rfl⟩ := D.surj w Y
    refine ⟨m + t • m0, fun g hg => ?_⟩
    have a1 : D.π w (∑ i, c i • τ i w g - x0 (P.φ w g) - (D.M.ρ (P.φ w g) m - m)) = 0 := by
      have := hY g hg
      simp only [map_sub, D.equiv, ← this]
      simp [Prod.snd_sum, Finset.sum_apply]
    rw [hk] at a1
    convert add_mem a1 (Submodule.sum_mem _ fun i (_ : i ∈ Finset.univ) => (N w).smul_mem (c i) (hτ i w g)) using 1

    simp only [Pi.add_apply, amitsur_d0_apply, map_sub, map_add (f := _), map_sum, he, smul_sub, Finset.sum_sub_distrib, map_smul ι (c _)]
    abel

end UpperTheory.V.Pa.B2
end

section

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

noncomputable section

namespace UpperTheory.V.Pa.B2

section Pull

variable {A Γ Γ' : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']

private def pull (p : Γ →* Γ') (hp : Continuous p) (M : FRep A Γ') : FRep A Γ where
  X := M.X
  ρ := M.ρ.comp p
  cont := M.cont.comp (hp.prodMap continuous_id)

variable (p : Γ ≃* Γ') (hp : Continuous p) (hq : Continuous p.symm) (M : FRep A Γ')

private def r1 : H1 M.ρ →ₗ[A] H1 (pull p.toMonoidHom hp M).ρ :=
  pairH1DecompositionMap M.ρ (pull p.toMonoidHom hp M).ρ p.toMonoidHom hp LinearMap.id continuous_id fun _ _ => rfl

private def r2 : H2 M.ρ →ₗ[A] H2 (pull p.toMonoidHom hp M).ρ :=
  compatiblePairH2 M.ρ (pull p.toMonoidHom hp M).ρ p.toMonoidHom hp LinearMap.id continuous_id fun _ _ => rfl

private theorem back (g : Γ') (m : M.X) : (pull p.toMonoidHom hp M).ρ (p.symm g) m = M.ρ g m := by
  show M.ρ (p.toMonoidHom (p.symm g)) m = M.ρ g m
  simp

include hq in
private theorem restriction_one_bijective : Function.Bijective (r1 p hp M) := by
  let s : H1 (pull p.toMonoidHom hp M).ρ →ₗ[A] H1 M.ρ :=
    pairH1DecompositionMap (pull p.toMonoidHom hp M).ρ M.ρ p.symm.toMonoidHom hq LinearMap.id continuous_id
      fun g m => back p hp M g m
  refine Function.bijective_iff_has_inverse.mpr ⟨s, fun x => ?_, fun x => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r1, pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (p.apply_symm_apply g)
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r1, pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (p.symm_apply_apply g)

include hq in
private theorem restriction_two_bijective : Function.Bijective (r2 p hp M) := by
  let s : H2 (pull p.toMonoidHom hp M).ρ →ₗ[A] H2 M.ρ :=
    compatiblePairH2 (pull p.toMonoidHom hp M).ρ M.ρ p.symm.toMonoidHom hq LinearMap.id continuous_id
      fun g m => back p hp M g m
  refine Function.bijective_iff_has_inverse.mpr ⟨s, fun x => ?_, fun x => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r2, compatiblePairH2, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (Prod.ext (p.apply_symm_apply g.1) (p.apply_symm_apply g.2))
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r2, compatiblePairH2, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (Prod.ext (p.symm_apply_apply g.1) (p.symm_apply_apply g.2))

private theorem card_H0_pullback_eq : Nat.card (H0 (pull p.toMonoidHom hp M).ρ) = Nat.card (H0 M.ρ) := by
  have e : H0 (pull p.toMonoidHom hp M).ρ = H0 M.ρ := by
    ext m
    simp only [H0, Representation.mem_invariants]
    constructor
    · intro h g
      rw [← back p hp M g m]
      exact h _
    · intro h g
      exact h (p g)
  rw [e]
  rfl

include hp hq in
private theorem finH_iso (l : ℕ) (h : FinH l Γ) : FinH l Γ' := by
  intro A _ M hl
  obtain ⟨h1, h2⟩ := h A (pull p.toMonoidHom hp M) hl
  exact ⟨Finite.of_equiv _ (Equiv.ofBijective _ (restriction_one_bijective p hp hq M)).symm,
    Finite.of_equiv _ (Equiv.ofBijective _ (restriction_two_bijective p hp hq M)).symm⟩

include hp hq in
private theorem onto_iso (l : ℕ) (h : SecondCohomologyRightExactModL l Γ) : SecondCohomologyRightExactModL l Γ' := by
  intro A _ M M' hl u hu hs y
  have hu' : ∀ (g : Γ) (m : (pull p.toMonoidHom hp M).X),
      u ((pull p.toMonoidHom hp M).ρ g m) = (pull p.toMonoidHom hp M').ρ g (u m) :=
    fun g m => hu (p g) m
  have key : ∀ x, r2 p hp M' (mapH2 M.ρ M'.ρ u continuous_of_discreteTopology hu x) =
      mapH2 (pull p.toMonoidHom hp M).ρ (pull p.toMonoidHom hp M').ρ u continuous_of_discreteTopology hu'
        (r2 p hp M x) := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [r2, compatiblePairH2, mapH2, Submodule.mapQ_apply]
    rfl
  obtain ⟨x', hx'⟩ := h A (pull p.toMonoidHom hp M) (pull p.toMonoidHom hp M') hl u hu' hs (r2 p hp M' y)
  obtain ⟨x, rfl⟩ := (restriction_two_bijective p hp hq M).2 x'
  refine ⟨x, (restriction_two_bijective p hp hq M').1 ?_⟩
  rw [key, hx']

end Pull

section Gl

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (e : G.Hom G') {A : Type} [CommRing A]

private theorem pl_φ (w : (plOf G).ι) (g : (plOf G).G w) : e.p ((plOf G).φ w g) = (plOf G').φ w g := by
  cases w with
  | inl v => exact e.φ v g
  | inr u => exact e.φu u g

private def pullD (D : Dat A (plOf G')) : Dat A (plOf G) where
  M := pull e.p e.cont D.M
  Q w := D.Q w
  π w := D.π w
  surj w := D.surj w
  equiv w g m := by
    have h := D.equiv w g m
    rw [← pl_φ e w g] at h
    exact h

end Gl

end UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.cohAxIso :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (e : G.Hom G') (d : ℕ) (dv : L.Vl → ℕ), Function.Injective e.p → CohAx G d dv → CohAx G' d dv := by
  intro l _ L G G' e d dv hinj hG
  haveI : T2Space G'.Γ := inferInstance
  let q : G.Γ ≃* G'.Γ := MulEquiv.ofBijective e.p ⟨hinj, e.surj⟩
  have hq : Continuous q := e.cont
  have hqs : Continuous q.symm :=
    (Continuous.homeoOfEquivCompactToT2 (f := q.toEquiv) e.cont).symm.continuous
  refine ⟨hG.sum, finH_iso q hq hqs l hG.fin, hG.finV, hG.finU, onto_iso q hq hqs l hG.onto, ?_,
    hG.leV, hG.leU, hG.ur, ?_⟩
  · obtain ⟨c, hc, hf⟩ := hG.ge
    refine ⟨fun i => e.p (c i), fun i => ⟨by rw [e.η]; exact (hc i).1, by rw [← map_mul, (hc i).2, map_one]⟩, ?_⟩
    intro A _ M hl
    have h := hf A (pull q.toMonoidHom hq M) hl
    rw [card_H0_pullback_eq] at h
    rw [Nat.card_congr (Equiv.ofBijective _ (restriction_two_bijective q hq hqs M)),
      Nat.card_congr (Equiv.ofBijective _ (restriction_one_bijective q hq hqs M))]
    exact h
  · intro A _ D hl
    have h := hG.ck A (pullD e D) hl
    have hc : ∀ x, D.loc2 x = (pullD e D).loc2 (r2 q hq D.M x) := by
      intro x
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      funext w
      simp only [Dat.loc2, LinearMap.pi_apply, r2, compatiblePairH2, Submodule.mapQ_apply]
      congr 1
      ext y
      show D.π w (z.1 ((plOf G').φ w y.1, (plOf G').φ w y.2)) =
        D.π w (z.1 (e.p ((plOf G).φ w y.1), e.p ((plOf G).φ w y.2)))
      rw [pl_φ e w y.1, pl_φ e w y.2]
    have hr : (pullD e D).loc2.range = D.loc2.range := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨x0, rfl⟩ := (restriction_two_bijective q hq hqs D.M).2 x
        exact ⟨x0, hc x0⟩
      · rintro ⟨x, rfl⟩
        exact ⟨r2 q hq D.M x, (hc x).symm⟩
    have h1 : Nat.card (pullD e D).Ck2 = Nat.card D.Ck2 := by
      show Nat.card (_ ⧸ (pullD e D).loc2.range) = Nat.card (_ ⧸ D.loc2.range)
      rw [hr]
      rfl
    rw [← h1]
    refine h.trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)))
    constructor
    · intro hf g m
      obtain ⟨g0, rfl⟩ := e.surj g
      rw [e.ε]
      exact hf g0 m
    · intro hf g m
      have := hf (e.p g) m
      rw [e.ε] at this
      exact this
end
end
