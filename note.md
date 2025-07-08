thanks to and many(seems most) lemmas have been put into mathlib, you can go to innerproductspace and other place to see the official provement.

complex is limited in proving, while rclike can use in most of the time

simp can turn RCLike.re (↑‖x i‖ * ↑‖x i‖) to ‖x i‖ * ‖x i‖ but i dont know why

isrorc and rclike seems dont have the abs directly use for \k, abs just use for im and re, so i use norm to replace abs

fun i ↦ still need to learn

field_simp