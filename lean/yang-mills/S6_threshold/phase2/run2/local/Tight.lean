import GAffEval
open GAff
-- exact upper end of G on the reference box, from its five integers: c + |a1|+|a2|+|a3| + e
-- = -1131454374408286180 + 1291460300591990 + 524007866667978 + 982203762417704 + 3258472002879632
theorem eq_ok : zle (ahi (gform ⟨2, 5, 81, 200, 2, 5, 41, 100, 63, 500, 77, 500⟩)) ⟨true, 1125398230475728876⟩ = true := by decide +kernel
theorem tight : zlt (ahi (gform ⟨2, 5, 81, 200, 2, 5, 41, 100, 63, 500, 77, 500⟩)) ⟨true, 1125398230475728876⟩ = true := by decide +kernel
