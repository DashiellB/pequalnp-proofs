import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1555

def lines (t : Fin 13) : Finset (Fin 13) := {t, t+1, t+3, t+9}

def base (t p : Fin 13) : Finset (Fin 13) :=
  match t.val, p.val with
  | 0, 0 => {4, 8}
  | 0, 1 => {8}
  | 0, 3 => {8}
  | 0, 9 => {8}
  | 1, 1 => {5}
  | 1, 2 => {5}
  | 1, 4 => {8}
  | 1, 10 => {5}
  | 2, 2 => {9}
  | 2, 3 => {8}
  | 2, 5 => {8}
  | 2, 11 => {8}
  | 3, 3 => {11}
  | 3, 4 => {11}
  | 3, 6 => {2}
  | 3, 12 => {11}
  | 4, 0 => {3, 12}
  | 4, 4 => {12}
  | 4, 5 => {12}
  | 4, 7 => {12}
  | 5, 1 => {7}
  | 5, 5 => {12}
  | 5, 6 => {7}
  | 5, 8 => {7}
  | 6, 2 => {4}
  | 6, 6 => {4}
  | 6, 7 => {3}
  | 6, 9 => {4}
  | 7, 3 => {12}
  | 7, 7 => {12}
  | 7, 8 => {6}
  | 7, 10 => {12}
  | 8, 4 => {10}
  | 8, 8 => {10}
  | 8, 9 => {10}
  | 8, 11 => {5}
  | 9, 5 => {6}
  | 9, 9 => {6}
  | 9, 10 => {1}
  | 9, 12 => {6}
  | 10, 0 => {1, 2}
  | 10, 6 => {1}
  | 10, 10 => {1}
  | 10, 11 => {1}
  | 11, 1 => {2}
  | 11, 7 => {2}
  | 11, 11 => {2}
  | 11, 12 => {9}
  | 12, 0 => {6, 9}
  | 12, 2 => {6}
  | 12, 8 => {6}
  | 12, 12 => {6}
  | _, _ => ∅

def Valid (L : Fin 13 → Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13)) : Prop :=
  (∀ t : Fin 13, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ (∀ v ∈ L t, decide (v = p ∨ v ∈ B t p) = true ↔ v = p) ∧
      (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p)) a = true ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p)) b = true)) ∧
    (∀ s s' : Fin 13, s ≠ 12 → s' ≠ 12 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) ∧
    (∀ s : Fin 13, s ≠ 12 → (((∃ p ∈ L 12 \ L s, (B 12 p ∩ L s).Nonempty) ∧ (∃ p ∈ L s \ L 12, (B s p ∩ L 12).Nonempty)) ↔ s = 3 ∨ s = 5)) ∧
    ((L 3 \ L 12).filter (fun p => (B 3 p ∩ L 12).Nonempty)) = {6} ∧ ((L 12 \ L 3).filter (fun p => (B 12 p ∩ L 3).Nonempty)) = {0, 2, 8} ∧
    ((L 5 \ L 12).filter (fun p => (B 5 p ∩ L 12).Nonempty)) = {5} ∧ ((L 12 \ L 5).filter (fun p => (B 12 p ∩ L 5).Nonempty)) = {0, 2, 12}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : Valid lines base := by
  unfold Valid
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | decide +kernel | skip
  intro s t hs ht hst
  fin_cases s <;> fin_cases t <;> first | contradiction | decide +kernel

def active (U : Fin 13 → Fin 13 → Finset (Fin 13)) (s t : Fin 13) :=
  (lines s \ lines t).filter (fun p => (U s p ∩ lines t).Nonempty)

theorem transfer (U : Fin 13 → Fin 13 → Finset (Fin 13))
    (eqn : ∀ s, ∀ p ∈ lines s, U s p = base s p) : Valid lines U := by
  have point := checked.1
  have noConflict := checked.2.1
  have conflicts := checked.2.2.1
  have filters := checked.2.2.2
  have hits (s t : Fin 13) :
      (∃ p ∈ lines s \ lines t, (U s p ∩ lines t).Nonempty) ↔
      (∃ p ∈ lines s \ lines t, (base s p ∩ lines t).Nonempty) := by
    constructor <;> rintro ⟨p, hp, hw⟩ <;> refine ⟨p, hp, ?_⟩
    all_goals simpa only [eqn s p (Finset.mem_sdiff.mp hp).1] using hw
  have same (s t : Fin 13) : active U s t = active base s t := by
    unfold active
    apply Finset.filter_congr
    intro p hp
    rw [eqn s p (Finset.mem_sdiff.mp hp).1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t p hp
    rw [eqn t p hp]
    exact point t p hp
  · intro s t hs ht hst
    simpa only [hits] using noConflict s t hs ht hst
  · intro s hs
    simpa only [hits] using conflicts s hs
  · change active U 3 12 = _ ∧ active U 12 3 = _ ∧ active U 5 12 = _ ∧ active U 12 5 = _
    simp only [same]
    simpa [active] using filters

end PEqualNP.Outside.L_meta_1555

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1555 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ B : Fin 13 → Fin 13 → Finset (Fin 13),
    (B 0 0 = {4, 8} ∧ B 0 1 = {8} ∧ B 0 3 = {8} ∧ B 0 9 = {8}) →
    (B 1 1 = {5} ∧ B 1 2 = {5} ∧ B 1 4 = {8} ∧ B 1 10 = {5}) →
    (B 2 2 = {9} ∧ B 2 3 = {8} ∧ B 2 5 = {8} ∧ B 2 11 = {8}) →
    (B 3 3 = {11} ∧ B 3 4 = {11} ∧ B 3 6 = {2} ∧ B 3 12 = {11}) →
    (B 4 0 = {3, 12} ∧ B 4 4 = {12} ∧ B 4 5 = {12} ∧ B 4 7 = {12}) →
    (B 5 1 = {7} ∧ B 5 5 = {12} ∧ B 5 6 = {7} ∧ B 5 8 = {7}) →
    (B 6 2 = {4} ∧ B 6 6 = {4} ∧ B 6 7 = {3} ∧ B 6 9 = {4}) →
    (B 7 3 = {12} ∧ B 7 7 = {12} ∧ B 7 8 = {6} ∧ B 7 10 = {12}) →
    (B 8 4 = {10} ∧ B 8 8 = {10} ∧ B 8 9 = {10} ∧ B 8 11 = {5}) →
    (B 9 5 = {6} ∧ B 9 9 = {6} ∧ B 9 10 = {1} ∧ B 9 12 = {6}) →
    (B 10 0 = {1, 2} ∧ B 10 6 = {1} ∧ B 10 10 = {1} ∧ B 10 11 = {1}) →
    (B 11 1 = {2} ∧ B 11 7 = {2} ∧ B 11 11 = {2} ∧ B 11 12 = {9}) →
    (B 12 0 = {6, 9} ∧ B 12 2 = {6} ∧ B 12 8 = {6} ∧ B 12 12 = {6}) →
    (∀ t : Fin 13, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ (∀ v ∈ L t, decide (v = p ∨ v ∈ B t p) = true ↔ v = p) ∧
      (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p)) a = true ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p)) b = true)) ∧
    (∀ s s' : Fin 13, s ≠ 12 → s' ≠ 12 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) ∧
    (∀ s : Fin 13, s ≠ 12 → (((∃ p ∈ L 12 \ L s, (B 12 p ∩ L s).Nonempty) ∧ (∃ p ∈ L s \ L 12, (B s p ∩ L 12).Nonempty)) ↔ s = 3 ∨ s = 5)) ∧
    ((L 3 \ L 12).filter (fun p => (B 3 p ∩ L 12).Nonempty)) = {6} ∧ ((L 12 \ L 3).filter (fun p => (B 12 p ∩ L 3).Nonempty)) = {0, 2, 8} ∧
    ((L 5 \ L 12).filter (fun p => (B 5 p ∩ L 12).Nonempty)) = {5} ∧ ((L 12 \ L 5).filter (fun p => (B 12 p ∩ L 5).Nonempty)) = {0, 2, 12} := by
  intro L hL B r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
  have hl : L = PEqualNP.Outside.L_meta_1555.lines := funext hL
  subst L
  apply PEqualNP.Outside.L_meta_1555.transfer
  rcases r0 with ⟨h0a, h0b, h0c, h0d⟩
  rcases r1 with ⟨h1a, h1b, h1c, h1d⟩
  rcases r2 with ⟨h2a, h2b, h2c, h2d⟩
  rcases r3 with ⟨h3a, h3b, h3c, h3d⟩
  rcases r4 with ⟨h4a, h4b, h4c, h4d⟩
  rcases r5 with ⟨h5a, h5b, h5c, h5d⟩
  rcases r6 with ⟨h6a, h6b, h6c, h6d⟩
  rcases r7 with ⟨h7a, h7b, h7c, h7d⟩
  rcases r8 with ⟨h8a, h8b, h8c, h8d⟩
  rcases r9 with ⟨h9a, h9b, h9c, h9d⟩
  rcases r10 with ⟨h10a, h10b, h10c, h10d⟩
  rcases r11 with ⟨h11a, h11b, h11c, h11d⟩
  rcases r12 with ⟨h12a, h12b, h12c, h12d⟩
  intro t p hp
  fin_cases t <;> fin_cases p
  all_goals first | assumption | exact absurd hp (by decide)
