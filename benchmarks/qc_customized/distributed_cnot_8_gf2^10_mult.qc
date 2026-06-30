# Hyperedge cut (ebits): 45

# Actual ebits used (Synthesis): 242
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^10_mult.qc):
#   Qubits: 30
#   H: 38
#   T: 700
#   cnot: 609
#   Depth: 246
#   T depth: 119
# Result (100.508ms):
#   Qubits: 514
#   H: 522
#   S: 25
#   T: 410
#   Z: 6
#   cnot: 1374
#   cz: 242
#   measure: 484
#   reset: 484
#   Depth: 487
#   T depth: 109


# Result Circuit
.v a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell180 bell181 bell182 bell183 bell184 bell185 bell186 bell187 bell188 bell189 bell19 bell190 bell191 bell192 bell193 bell194 bell195 bell196 bell197 bell198 bell199 bell2 bell20 bell200 bell201 bell202 bell203 bell204 bell205 bell206 bell207 bell208 bell209 bell21 bell210 bell211 bell212 bell213 bell214 bell215 bell216 bell217 bell218 bell219 bell22 bell220 bell221 bell222 bell223 bell224 bell225 bell226 bell227 bell228 bell229 bell23 bell230 bell231 bell232 bell233 bell234 bell235 bell236 bell237 bell238 bell239 bell24 bell240 bell241 bell242 bell243 bell244 bell245 bell246 bell247 bell248 bell249 bell25 bell250 bell251 bell252 bell253 bell254 bell255 bell256 bell257 bell258 bell259 bell26 bell260 bell261 bell262 bell263 bell264 bell265 bell266 bell267 bell268 bell269 bell27 bell270 bell271 bell272 bell273 bell274 bell275 bell276 bell277 bell278 bell279 bell28 bell280 bell281 bell282 bell283 bell284 bell285 bell286 bell287 bell288 bell289 bell29 bell290 bell291 bell292 bell293 bell294 bell295 bell296 bell297 bell298 bell299 bell3 bell30 bell300 bell301 bell302 bell303 bell304 bell305 bell306 bell307 bell308 bell309 bell31 bell310 bell311 bell312 bell313 bell314 bell315 bell316 bell317 bell318 bell319 bell32 bell320 bell321 bell322 bell323 bell324 bell325 bell326 bell327 bell328 bell329 bell33 bell330 bell331 bell332 bell333 bell334 bell335 bell336 bell337 bell338 bell339 bell34 bell340 bell341 bell342 bell343 bell344 bell345 bell346 bell347 bell348 bell349 bell35 bell350 bell351 bell352 bell353 bell354 bell355 bell356 bell357 bell358 bell359 bell36 bell360 bell361 bell362 bell363 bell364 bell365 bell366 bell367 bell368 bell369 bell37 bell370 bell371 bell372 bell373 bell374 bell375 bell376 bell377 bell378 bell379 bell38 bell380 bell381 bell382 bell383 bell384 bell385 bell386 bell387 bell388 bell389 bell39 bell390 bell391 bell392 bell393 bell394 bell395 bell396 bell397 bell398 bell399 bell4 bell40 bell400 bell401 bell402 bell403 bell404 bell405 bell406 bell407 bell408 bell409 bell41 bell410 bell411 bell412 bell413 bell414 bell415 bell416 bell417 bell418 bell419 bell42 bell420 bell421 bell422 bell423 bell424 bell425 bell426 bell427 bell428 bell429 bell43 bell430 bell431 bell432 bell433 bell434 bell435 bell436 bell437 bell438 bell439 bell44 bell440 bell441 bell442 bell443 bell444 bell445 bell446 bell447 bell448 bell449 bell45 bell450 bell451 bell452 bell453 bell454 bell455 bell456 bell457 bell458 bell459 bell46 bell460 bell461 bell462 bell463 bell464 bell465 bell466 bell467 bell468 bell469 bell47 bell470 bell471 bell472 bell473 bell474 bell475 bell476 bell477 bell478 bell479 bell48 bell480 bell481 bell482 bell483 bell49 bell5 bell50 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 c9
.o a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
BEGIN 
H c0
H c1
H c2
H c3
H c4
H c5
H c6
H c7
H c8
T c0
H bell0
cnot bell0 bell1
cnot a9 bell1
measure bell1
cnot bell1 bell0
cnot bell0 c0
T* c0
H bell2
cnot bell2 bell3
cnot b1 bell3
measure bell3
cnot bell3 bell2
cnot bell2 c0
T c0
cnot bell0 c0
H bell0
measure bell0
cz bell0 a9
T* c0
H bell4
cnot bell4 bell5
cnot a8 bell5
measure bell5
cnot bell5 bell4
cnot bell4 c0
cnot bell2 c0
H bell2
measure bell2
cz bell2 b1
T* c0
H bell6
cnot bell6 bell7
cnot b2 bell7
measure bell7
cnot bell7 bell6
cnot bell6 c0
T c0
cnot bell4 c0
H bell4
measure bell4
cz bell4 a8
T* c0
H bell8
cnot bell8 bell9
cnot a7 bell9
measure bell9
cnot bell9 bell8
cnot bell8 c0
cnot bell6 c0
H bell6
measure bell6
cz bell6 b2
T* c0
H bell10
cnot bell10 bell11
cnot b3 bell11
measure bell11
cnot bell11 bell10
cnot bell10 c0
T c0
cnot bell8 c0
H bell8
measure bell8
cz bell8 a7
T* c0
H bell12
cnot bell12 bell13
cnot a6 bell13
measure bell13
cnot bell13 bell12
cnot bell12 c0
cnot bell10 c0
H bell10
measure bell10
cz bell10 b3
T* c0
H bell14
cnot bell14 bell15
cnot b4 bell15
measure bell15
cnot bell15 bell14
cnot bell14 c0
T c0
cnot bell12 c0
H bell12
measure bell12
cz bell12 a6
T* c0
H bell16
cnot bell16 bell17
cnot a5 bell17
measure bell17
cnot bell17 bell16
cnot bell16 c0
cnot bell14 c0
H bell14
measure bell14
cz bell14 b4
T* c0
H bell18
cnot bell18 bell19
cnot b5 bell19
measure bell19
cnot bell19 bell18
cnot bell18 c0
T c0
cnot bell16 c0
H bell16
measure bell16
cz bell16 a5
T* c0
H bell20
cnot bell20 bell21
cnot a4 bell21
measure bell21
cnot bell21 bell20
cnot bell20 c0
cnot bell18 c0
H bell18
measure bell18
cz bell18 b5
T* c0
H bell22
cnot bell22 bell23
cnot b6 bell23
measure bell23
cnot bell23 bell22
cnot bell22 c0
T c0
cnot bell20 c0
H bell20
measure bell20
cz bell20 a4
T* c0
H bell24
cnot bell24 bell25
cnot a3 bell25
measure bell25
cnot bell25 bell24
cnot bell24 c0
cnot bell22 c0
H bell22
measure bell22
cz bell22 b6
T* c0
H bell26
cnot bell26 bell27
cnot b7 bell27
measure bell27
cnot bell27 bell26
cnot bell26 c0
T c0
cnot bell24 c0
H bell24
measure bell24
cz bell24 a3
T* c0
H bell28
cnot bell28 bell29
cnot a2 bell29
measure bell29
cnot bell29 bell28
cnot bell28 c0
cnot bell26 c0
H bell26
measure bell26
cz bell26 b7
T* c0
H bell30
cnot bell30 bell31
cnot b8 bell31
measure bell31
cnot bell31 bell30
cnot bell30 c0
T c0
cnot bell28 c0
H bell28
measure bell28
cz bell28 a2
T* c0
H bell32
cnot bell32 bell33
cnot a1 bell33
measure bell33
cnot bell33 bell32
cnot bell32 c0
cnot bell30 c0
H bell30
measure bell30
cz bell30 b8
T* c0
H bell34
cnot bell34 bell35
cnot b9 bell35
measure bell35
cnot bell35 bell34
cnot bell34 c0
T c0
cnot bell32 c0
H bell32
measure bell32
cz bell32 a1
T* c0
cnot bell34 c0
H bell34
measure bell34
cz bell34 b9
H c0
H bell36
cnot bell36 bell37
cnot a9 bell37
measure bell37
cnot bell37 bell36
cnot bell36 c1
T* c1
H bell38
cnot bell38 bell39
cnot b2 bell39
measure bell39
cnot bell39 bell38
cnot bell38 c1
T c1
cnot bell36 c1
H bell36
measure bell36
cz bell36 a9
T* c1
H bell40
cnot bell40 bell41
cnot a8 bell41
measure bell41
cnot bell41 bell40
cnot bell40 c1
cnot bell38 c1
H bell38
measure bell38
cz bell38 b2
T* c1
H bell42
cnot bell42 bell43
cnot b3 bell43
measure bell43
cnot bell43 bell42
cnot bell42 c1
T c1
cnot bell40 c1
H bell40
measure bell40
cz bell40 a8
T* c1
H bell44
cnot bell44 bell45
cnot a7 bell45
measure bell45
cnot bell45 bell44
cnot bell44 c1
cnot bell42 c1
H bell42
measure bell42
cz bell42 b3
T* c1
H bell46
cnot bell46 bell47
cnot b4 bell47
measure bell47
cnot bell47 bell46
cnot bell46 c1
T c1
cnot bell44 c1
H bell44
measure bell44
cz bell44 a7
T* c1
H bell48
cnot bell48 bell49
cnot a6 bell49
measure bell49
cnot bell49 bell48
cnot bell48 c1
cnot bell46 c1
H bell46
measure bell46
cz bell46 b4
T* c1
H bell50
cnot bell50 bell51
cnot b5 bell51
measure bell51
cnot bell51 bell50
cnot bell50 c1
T c1
cnot bell48 c1
H bell48
measure bell48
cz bell48 a6
T* c1
H bell52
cnot bell52 bell53
cnot a5 bell53
measure bell53
cnot bell53 bell52
cnot bell52 c1
cnot bell50 c1
H bell50
measure bell50
cz bell50 b5
T* c1
H bell54
cnot bell54 bell55
cnot b6 bell55
measure bell55
cnot bell55 bell54
cnot bell54 c1
T c1
cnot bell52 c1
H bell52
measure bell52
cz bell52 a5
T* c1
H bell56
cnot bell56 bell57
cnot a4 bell57
measure bell57
cnot bell57 bell56
cnot bell56 c1
cnot bell54 c1
H bell54
measure bell54
cz bell54 b6
T* c1
H bell58
cnot bell58 bell59
cnot b7 bell59
measure bell59
cnot bell59 bell58
cnot bell58 c1
T c1
cnot bell56 c1
H bell56
measure bell56
cz bell56 a4
T* c1
H bell60
cnot bell60 bell61
cnot a3 bell61
measure bell61
cnot bell61 bell60
cnot bell60 c1
cnot bell58 c1
H bell58
measure bell58
cz bell58 b7
T* c1
H bell62
cnot bell62 bell63
cnot b8 bell63
measure bell63
cnot bell63 bell62
cnot bell62 c1
T c1
cnot bell60 c1
H bell60
measure bell60
cz bell60 a3
T* c1
H bell64
cnot bell64 bell65
cnot a2 bell65
measure bell65
cnot bell65 bell64
cnot bell64 c1
cnot bell62 c1
H bell62
measure bell62
cz bell62 b8
T* c1
H bell66
cnot bell66 bell67
cnot b9 bell67
measure bell67
cnot bell67 bell66
cnot bell66 c1
T c1
cnot bell64 c1
H bell64
measure bell64
cz bell64 a2
T* c1
cnot bell66 c1
H bell66
measure bell66
cz bell66 b9
H c1
T* c2
H bell68
cnot bell68 bell69
cnot a9 bell69
measure bell69
cnot bell69 bell68
cnot bell68 c2
T* c2
H bell70
cnot bell70 bell71
cnot b3 bell71
measure bell71
cnot bell71 bell70
cnot bell70 c2
T c2
cnot bell68 c2
H bell68
measure bell68
cz bell68 a9
T* c2
H bell72
cnot bell72 bell73
cnot a8 bell73
measure bell73
cnot bell73 bell72
cnot bell72 c2
cnot bell70 c2
H bell70
measure bell70
cz bell70 b3
T* c2
H bell74
cnot bell74 bell75
cnot b4 bell75
measure bell75
cnot bell75 bell74
cnot bell74 c2
T c2
cnot bell72 c2
H bell72
measure bell72
cz bell72 a8
T* c2
H bell76
cnot bell76 bell77
cnot a7 bell77
measure bell77
cnot bell77 bell76
cnot bell76 c2
cnot bell74 c2
H bell74
measure bell74
cz bell74 b4
T* c2
H bell78
cnot bell78 bell79
cnot b5 bell79
measure bell79
cnot bell79 bell78
cnot bell78 c2
T c2
cnot bell76 c2
H bell76
measure bell76
cz bell76 a7
T* c2
H bell80
cnot bell80 bell81
cnot a6 bell81
measure bell81
cnot bell81 bell80
cnot bell80 c2
cnot bell78 c2
H bell78
measure bell78
cz bell78 b5
T* c2
H bell82
cnot bell82 bell83
cnot b6 bell83
measure bell83
cnot bell83 bell82
cnot bell82 c2
T c2
cnot bell80 c2
H bell80
measure bell80
cz bell80 a6
T* c2
H bell84
cnot bell84 bell85
cnot a5 bell85
measure bell85
cnot bell85 bell84
cnot bell84 c2
cnot bell82 c2
H bell82
measure bell82
cz bell82 b6
T* c2
H bell86
cnot bell86 bell87
cnot b7 bell87
measure bell87
cnot bell87 bell86
cnot bell86 c2
T c2
cnot bell84 c2
H bell84
measure bell84
cz bell84 a5
T* c2
H bell88
cnot bell88 bell89
cnot a4 bell89
measure bell89
cnot bell89 bell88
cnot bell88 c2
cnot bell86 c2
H bell86
measure bell86
cz bell86 b7
T* c2
H bell90
cnot bell90 bell91
cnot b8 bell91
measure bell91
cnot bell91 bell90
cnot bell90 c2
T c2
cnot bell88 c2
H bell88
measure bell88
cz bell88 a4
T* c2
H bell92
cnot bell92 bell93
cnot a3 bell93
measure bell93
cnot bell93 bell92
cnot bell92 c2
cnot bell90 c2
H bell90
measure bell90
cz bell90 b8
T* c2
H bell94
cnot bell94 bell95
cnot b9 bell95
measure bell95
cnot bell95 bell94
cnot bell94 c2
T c2
cnot bell92 c2
H bell92
measure bell92
cz bell92 a3
T* c2
cnot bell94 c2
H bell94
measure bell94
cz bell94 b9
H c2
S* c3
H bell96
cnot bell96 bell97
cnot a9 bell97
measure bell97
cnot bell97 bell96
cnot bell96 c3
T* c3
H bell98
cnot bell98 bell99
cnot b4 bell99
measure bell99
cnot bell99 bell98
cnot bell98 c3
T c3
cnot bell96 c3
H bell96
measure bell96
cz bell96 a9
T* c3
H bell100
cnot bell100 bell101
cnot a8 bell101
measure bell101
cnot bell101 bell100
cnot bell100 c3
cnot bell98 c3
H bell98
measure bell98
cz bell98 b4
T* c3
H bell102
cnot bell102 bell103
cnot b5 bell103
measure bell103
cnot bell103 bell102
cnot bell102 c3
T c3
cnot bell100 c3
H bell100
measure bell100
cz bell100 a8
T* c3
H bell104
cnot bell104 bell105
cnot a7 bell105
measure bell105
cnot bell105 bell104
cnot bell104 c3
cnot bell102 c3
H bell102
measure bell102
cz bell102 b5
T* c3
H bell106
cnot bell106 bell107
cnot b6 bell107
measure bell107
cnot bell107 bell106
cnot bell106 c3
T c3
cnot bell104 c3
H bell104
measure bell104
cz bell104 a7
T* c3
H bell108
cnot bell108 bell109
cnot a6 bell109
measure bell109
cnot bell109 bell108
cnot bell108 c3
cnot bell106 c3
H bell106
measure bell106
cz bell106 b6
T* c3
H bell110
cnot bell110 bell111
cnot b7 bell111
measure bell111
cnot bell111 bell110
cnot bell110 c3
T c3
cnot bell108 c3
H bell108
measure bell108
cz bell108 a6
T* c3
H bell112
cnot bell112 bell113
cnot a5 bell113
measure bell113
cnot bell113 bell112
cnot bell112 c3
cnot bell110 c3
H bell110
measure bell110
cz bell110 b7
T* c3
H bell114
cnot bell114 bell115
cnot b8 bell115
measure bell115
cnot bell115 bell114
cnot bell114 c3
T c3
cnot bell112 c3
H bell112
measure bell112
cz bell112 a5
T* c3
H bell116
cnot bell116 bell117
cnot a4 bell117
measure bell117
cnot bell117 bell116
cnot bell116 c3
cnot bell114 c3
H bell114
measure bell114
cz bell114 b8
T* c3
H bell118
cnot bell118 bell119
cnot b9 bell119
measure bell119
cnot bell119 bell118
cnot bell118 c3
T c3
cnot bell116 c3
H bell116
measure bell116
cz bell116 a4
T* c3
cnot bell118 c3
H bell118
measure bell118
cz bell118 b9
H c3
T c4
Z c4
H bell120
cnot bell120 bell121
cnot a9 bell121
measure bell121
cnot bell121 bell120
cnot bell120 c4
T* c4
H bell122
cnot bell122 bell123
cnot b5 bell123
measure bell123
cnot bell123 bell122
cnot bell122 c4
T c4
cnot bell120 c4
T* c4
H bell124
cnot bell124 bell125
cnot a8 bell125
measure bell125
cnot bell125 bell124
cnot bell124 c4
cnot bell122 c4
T* c4
H bell126
cnot bell126 bell127
cnot b6 bell127
measure bell127
cnot bell127 bell126
cnot bell126 c4
T c4
cnot bell124 c4
T* c4
H bell128
cnot bell128 bell129
cnot a7 bell129
measure bell129
cnot bell129 bell128
cnot bell128 c4
cnot bell126 c4
T* c4
H bell130
cnot bell130 bell131
cnot b7 bell131
measure bell131
cnot bell131 bell130
cnot bell130 c4
T c4
cnot bell128 c4
T* c4
H bell132
cnot bell132 bell133
cnot a6 bell133
measure bell133
cnot bell133 bell132
cnot bell132 c4
cnot bell130 c4
T* c4
H bell134
cnot bell134 bell135
cnot b8 bell135
measure bell135
cnot bell135 bell134
cnot bell134 c4
T c4
cnot bell132 c4
T* c4
H bell136
cnot bell136 bell137
cnot a5 bell137
measure bell137
cnot bell137 bell136
cnot bell136 c4
cnot bell134 c4
T* c4
H bell138
cnot bell138 bell139
cnot b9 bell139
measure bell139
cnot bell139 bell138
cnot bell138 c4
T c4
cnot bell136 c4
T* c4
cnot bell138 c4
H c4
Z c5
cnot bell120 c5
T* c5
cnot bell126 c5
T c5
cnot bell120 c5
H bell120
measure bell120
cz bell120 a9
T* c5
cnot bell124 c5
cnot bell126 c5
H bell126
measure bell126
cz bell126 b6
T* c5
cnot bell130 c5
T c5
cnot bell124 c5
H bell124
measure bell124
cz bell124 a8
T* c5
cnot bell128 c5
cnot bell130 c5
H bell130
measure bell130
cz bell130 b7
T* c5
cnot bell134 c5
T c5
cnot bell128 c5
H bell128
measure bell128
cz bell128 a7
T* c5
cnot bell132 c5
cnot bell134 c5
H bell134
measure bell134
cz bell134 b8
T* c5
cnot bell138 c5
T c5
cnot bell132 c5
H bell132
measure bell132
cz bell132 a6
T* c5
cnot bell138 c5
H bell138
measure bell138
cz bell138 b9
H c5
T* c6
Z c6
H bell140
cnot bell140 bell141
cnot a9 bell141
measure bell141
cnot bell141 bell140
cnot bell140 c6
T* c6
H bell142
cnot bell142 bell143
cnot b7 bell143
measure bell143
cnot bell143 bell142
cnot bell142 c6
T c6
cnot bell140 c6
T* c6
H bell144
cnot bell144 bell145
cnot a8 bell145
measure bell145
cnot bell145 bell144
cnot bell144 c6
cnot bell142 c6
T* c6
H bell146
cnot bell146 bell147
cnot b8 bell147
measure bell147
cnot bell147 bell146
cnot bell146 c6
T c6
cnot bell144 c6
T* c6
H bell148
cnot bell148 bell149
cnot a7 bell149
measure bell149
cnot bell149 bell148
cnot bell148 c6
cnot bell146 c6
T* c6
H bell150
cnot bell150 bell151
cnot b9 bell151
measure bell151
cnot bell151 bell150
cnot bell150 c6
T c6
cnot bell148 c6
T* c6
cnot bell150 c6
H c6
S c7
cnot bell140 c7
T* c7
cnot bell146 c7
T c7
cnot bell140 c7
H bell140
measure bell140
cz bell140 a9
T* c7
cnot bell144 c7
cnot bell146 c7
H bell146
measure bell146
cz bell146 b8
T* c7
cnot bell150 c7
T c7
cnot bell144 c7
H bell144
measure bell144
cz bell144 a8
T* c7
cnot bell150 c7
H bell150
measure bell150
cz bell150 b9
H c7
T c8
H bell152
cnot bell152 bell153
cnot a9 bell153
measure bell153
cnot bell153 bell152
cnot bell152 c8
T* c8
H bell154
cnot bell154 bell155
cnot b9 bell155
measure bell155
cnot bell155 bell154
cnot bell154 c8
T c8
cnot bell152 c8
H bell152
measure bell152
cz bell152 a9
T* c8
cnot bell154 c8
H bell154
measure bell154
cz bell154 b9
H c8
cnot c7 c0
cnot c8 c1
H bell156
cnot bell156 bell157
cnot c6 bell157
measure bell157
cnot bell157 bell156
cnot bell156 c9
H bell156
measure bell156
cz bell156 c6
cnot c5 c8
H bell158
cnot bell158 bell159
cnot c4 bell159
measure bell159
cnot bell159 bell158
cnot bell158 c7
H bell158
measure bell158
cz bell158 c4
cnot c3 c6
H bell160
cnot bell160 bell161
cnot c2 bell161
measure bell161
cnot bell161 bell160
cnot bell160 c5
H bell160
measure bell160
cz bell160 c2
cnot c1 c4
cnot c0 c3
H c0
H c1
H c2
H c3
H c4
H c5
H c6
H c7
H c8
H c9
T c0
H bell162
cnot bell162 bell163
cnot a0 bell163
measure bell163
cnot bell163 bell162
cnot bell162 c0
T* c0
H bell164
cnot bell164 bell165
cnot b0 bell165
measure bell165
cnot bell165 bell164
cnot bell164 c0
T c0
cnot bell162 c0
H bell162
measure bell162
cz bell162 a0
T* c0
cnot bell164 c0
H bell164
measure bell164
cz bell164 b0
H c0
S c1
H bell166
cnot bell166 bell167
cnot a1 bell167
measure bell167
cnot bell167 bell166
cnot bell166 c1
T* c1
H bell168
cnot bell168 bell169
cnot b0 bell169
measure bell169
cnot bell169 bell168
cnot bell168 c1
T c1
cnot bell166 c1
H bell166
measure bell166
cz bell166 a1
T* c1
H bell170
cnot bell170 bell171
cnot a0 bell171
measure bell171
cnot bell171 bell170
cnot bell170 c1
cnot bell168 c1
H bell168
measure bell168
cz bell168 b0
T* c1
H bell172
cnot bell172 bell173
cnot b1 bell173
measure bell173
cnot bell173 bell172
cnot bell172 c1
T c1
cnot bell170 c1
H bell170
measure bell170
cz bell170 a0
T* c1
cnot bell172 c1
H bell172
measure bell172
cz bell172 b1
H c1
T* c2
Z c2
H bell174
cnot bell174 bell175
cnot a2 bell175
measure bell175
cnot bell175 bell174
cnot bell174 c2
T* c2
cnot b0 c2
T c2
cnot bell174 c2
H bell174
measure bell174
cz bell174 a2
T* c2
H bell176
cnot bell176 bell177
cnot a1 bell177
measure bell177
cnot bell177 bell176
cnot bell176 c2
cnot b0 c2
T* c2
H bell178
cnot bell178 bell179
cnot b1 bell179
measure bell179
cnot bell179 bell178
cnot bell178 c2
T c2
cnot bell176 c2
H bell176
measure bell176
cz bell176 a1
T* c2
cnot a0 c2
cnot bell178 c2
H bell178
measure bell178
cz bell178 b1
T* c2
H bell180
cnot bell180 bell181
cnot b2 bell181
measure bell181
cnot bell181 bell180
cnot bell180 c2
T c2
cnot a0 c2
T* c2
cnot bell180 c2
H bell180
measure bell180
cz bell180 b2
H c2
Z c3
H bell182
cnot bell182 bell183
cnot a3 bell183
measure bell183
cnot bell183 bell182
cnot bell182 c3
T* c3
H bell184
cnot bell184 bell185
cnot b0 bell185
measure bell185
cnot bell185 bell184
cnot bell184 c3
T c3
cnot bell182 c3
H bell182
measure bell182
cz bell182 a3
T* c3
H bell186
cnot bell186 bell187
cnot a2 bell187
measure bell187
cnot bell187 bell186
cnot bell186 c3
cnot bell184 c3
H bell184
measure bell184
cz bell184 b0
T* c3
H bell188
cnot bell188 bell189
cnot b1 bell189
measure bell189
cnot bell189 bell188
cnot bell188 c3
T c3
cnot bell186 c3
H bell186
measure bell186
cz bell186 a2
T* c3
H bell190
cnot bell190 bell191
cnot a1 bell191
measure bell191
cnot bell191 bell190
cnot bell190 c3
cnot bell188 c3
H bell188
measure bell188
cz bell188 b1
T* c3
H bell192
cnot bell192 bell193
cnot b2 bell193
measure bell193
cnot bell193 bell192
cnot bell192 c3
T c3
cnot bell190 c3
H bell190
measure bell190
cz bell190 a1
T* c3
H bell194
cnot bell194 bell195
cnot a0 bell195
measure bell195
cnot bell195 bell194
cnot bell194 c3
cnot bell192 c3
H bell192
measure bell192
cz bell192 b2
T* c3
H bell196
cnot bell196 bell197
cnot b3 bell197
measure bell197
cnot bell197 bell196
cnot bell196 c3
T c3
cnot bell194 c3
H bell194
measure bell194
cz bell194 a0
T* c3
cnot bell196 c3
H bell196
measure bell196
cz bell196 b3
H c3
T c4
Z c4
H bell198
cnot bell198 bell199
cnot a4 bell199
measure bell199
cnot bell199 bell198
cnot bell198 c4
T* c4
H bell200
cnot bell200 bell201
cnot b0 bell201
measure bell201
cnot bell201 bell200
cnot bell200 c4
T c4
cnot bell198 c4
T* c4
H bell202
cnot bell202 bell203
cnot a3 bell203
measure bell203
cnot bell203 bell202
cnot bell202 c4
cnot bell200 c4
T* c4
H bell204
cnot bell204 bell205
cnot b1 bell205
measure bell205
cnot bell205 bell204
cnot bell204 c4
T c4
cnot bell202 c4
T* c4
H bell206
cnot bell206 bell207
cnot a2 bell207
measure bell207
cnot bell207 bell206
cnot bell206 c4
cnot bell204 c4
T* c4
H bell208
cnot bell208 bell209
cnot b2 bell209
measure bell209
cnot bell209 bell208
cnot bell208 c4
T c4
cnot bell206 c4
T* c4
H bell210
cnot bell210 bell211
cnot a1 bell211
measure bell211
cnot bell211 bell210
cnot bell210 c4
cnot bell208 c4
T* c4
H bell212
cnot bell212 bell213
cnot b3 bell213
measure bell213
cnot bell213 bell212
cnot bell212 c4
T c4
cnot bell210 c4
T* c4
H bell214
cnot bell214 bell215
cnot a0 bell215
measure bell215
cnot bell215 bell214
cnot bell214 c4
cnot bell212 c4
T* c4
H bell216
cnot bell216 bell217
cnot b4 bell217
measure bell217
cnot bell217 bell216
cnot bell216 c4
T c4
cnot bell214 c4
T* c4
cnot bell216 c4
H c4
S* c5
cnot bell136 c5
T* c5
cnot bell200 c5
T c5
cnot bell136 c5
H bell136
measure bell136
cz bell136 a5
T* c5
cnot bell198 c5
cnot bell200 c5
H bell200
measure bell200
cz bell200 b0
T* c5
cnot bell204 c5
T c5
cnot bell198 c5
H bell198
measure bell198
cz bell198 a4
T* c5
cnot bell202 c5
cnot bell204 c5
H bell204
measure bell204
cz bell204 b1
T* c5
cnot bell208 c5
T c5
cnot bell202 c5
H bell202
measure bell202
cz bell202 a3
T* c5
cnot bell206 c5
cnot bell208 c5
H bell208
measure bell208
cz bell208 b2
T* c5
cnot bell212 c5
T c5
cnot bell206 c5
H bell206
measure bell206
cz bell206 a2
T* c5
cnot bell210 c5
cnot bell212 c5
H bell212
measure bell212
cz bell212 b3
T* c5
cnot bell216 c5
T c5
cnot bell210 c5
H bell210
measure bell210
cz bell210 a1
T* c5
cnot bell214 c5
cnot bell216 c5
H bell216
measure bell216
cz bell216 b4
T* c5
cnot bell122 c5
T c5
cnot bell214 c5
H bell214
measure bell214
cz bell214 a0
T* c5
cnot bell122 c5
H bell122
measure bell122
cz bell122 b5
H c5
T* c6
H bell218
cnot bell218 bell219
cnot a6 bell219
measure bell219
cnot bell219 bell218
cnot bell218 c6
T* c6
H bell220
cnot bell220 bell221
cnot b0 bell221
measure bell221
cnot bell221 bell220
cnot bell220 c6
T c6
cnot bell218 c6
T* c6
H bell222
cnot bell222 bell223
cnot a5 bell223
measure bell223
cnot bell223 bell222
cnot bell222 c6
cnot bell220 c6
T* c6
H bell224
cnot bell224 bell225
cnot b1 bell225
measure bell225
cnot bell225 bell224
cnot bell224 c6
T c6
cnot bell222 c6
T* c6
H bell226
cnot bell226 bell227
cnot a4 bell227
measure bell227
cnot bell227 bell226
cnot bell226 c6
cnot bell224 c6
T* c6
H bell228
cnot bell228 bell229
cnot b2 bell229
measure bell229
cnot bell229 bell228
cnot bell228 c6
T c6
cnot bell226 c6
T* c6
H bell230
cnot bell230 bell231
cnot a3 bell231
measure bell231
cnot bell231 bell230
cnot bell230 c6
cnot bell228 c6
T* c6
H bell232
cnot bell232 bell233
cnot b3 bell233
measure bell233
cnot bell233 bell232
cnot bell232 c6
T c6
cnot bell230 c6
T* c6
H bell234
cnot bell234 bell235
cnot a2 bell235
measure bell235
cnot bell235 bell234
cnot bell234 c6
cnot bell232 c6
T* c6
H bell236
cnot bell236 bell237
cnot b4 bell237
measure bell237
cnot bell237 bell236
cnot bell236 c6
T c6
cnot bell234 c6
T* c6
H bell238
cnot bell238 bell239
cnot a1 bell239
measure bell239
cnot bell239 bell238
cnot bell238 c6
cnot bell236 c6
T* c6
H bell240
cnot bell240 bell241
cnot b5 bell241
measure bell241
cnot bell241 bell240
cnot bell240 c6
T c6
cnot bell238 c6
T* c6
H bell242
cnot bell242 bell243
cnot a0 bell243
measure bell243
cnot bell243 bell242
cnot bell242 c6
cnot bell240 c6
T* c6
H bell244
cnot bell244 bell245
cnot b6 bell245
measure bell245
cnot bell245 bell244
cnot bell244 c6
T c6
cnot bell242 c6
T* c6
cnot bell244 c6
H c6
cnot bell148 c7
T* c7
cnot bell220 c7
T c7
cnot bell148 c7
H bell148
measure bell148
cz bell148 a7
T* c7
cnot bell218 c7
cnot bell220 c7
H bell220
measure bell220
cz bell220 b0
T* c7
cnot bell224 c7
T c7
cnot bell218 c7
H bell218
measure bell218
cz bell218 a6
T* c7
cnot bell222 c7
cnot bell224 c7
H bell224
measure bell224
cz bell224 b1
T* c7
cnot bell228 c7
T c7
cnot bell222 c7
H bell222
measure bell222
cz bell222 a5
T* c7
cnot bell226 c7
cnot bell228 c7
H bell228
measure bell228
cz bell228 b2
T* c7
cnot bell232 c7
T c7
cnot bell226 c7
H bell226
measure bell226
cz bell226 a4
T* c7
cnot bell230 c7
cnot bell232 c7
H bell232
measure bell232
cz bell232 b3
T* c7
cnot bell236 c7
T c7
cnot bell230 c7
H bell230
measure bell230
cz bell230 a3
T* c7
cnot bell234 c7
cnot bell236 c7
H bell236
measure bell236
cz bell236 b4
T* c7
cnot bell240 c7
T c7
cnot bell234 c7
H bell234
measure bell234
cz bell234 a2
T* c7
cnot bell238 c7
cnot bell240 c7
H bell240
measure bell240
cz bell240 b5
T* c7
cnot bell244 c7
T c7
cnot bell238 c7
H bell238
measure bell238
cz bell238 a1
T* c7
cnot bell242 c7
cnot bell244 c7
H bell244
measure bell244
cz bell244 b6
T* c7
cnot bell142 c7
T c7
cnot bell242 c7
H bell242
measure bell242
cz bell242 a0
T* c7
cnot bell142 c7
H bell142
measure bell142
cz bell142 b7
H c7
T c8
H bell246
cnot bell246 bell247
cnot a8 bell247
measure bell247
cnot bell247 bell246
cnot bell246 c8
T* c8
H bell248
cnot bell248 bell249
cnot b0 bell249
measure bell249
cnot bell249 bell248
cnot bell248 c8
T c8
cnot bell246 c8
H bell246
measure bell246
cz bell246 a8
T* c8
H bell250
cnot bell250 bell251
cnot a7 bell251
measure bell251
cnot bell251 bell250
cnot bell250 c8
cnot bell248 c8
H bell248
measure bell248
cz bell248 b0
T* c8
H bell252
cnot bell252 bell253
cnot b1 bell253
measure bell253
cnot bell253 bell252
cnot bell252 c8
T c8
cnot bell250 c8
H bell250
measure bell250
cz bell250 a7
T* c8
H bell254
cnot bell254 bell255
cnot a6 bell255
measure bell255
cnot bell255 bell254
cnot bell254 c8
cnot bell252 c8
H bell252
measure bell252
cz bell252 b1
T* c8
H bell256
cnot bell256 bell257
cnot b2 bell257
measure bell257
cnot bell257 bell256
cnot bell256 c8
T c8
cnot bell254 c8
H bell254
measure bell254
cz bell254 a6
T* c8
H bell258
cnot bell258 bell259
cnot a5 bell259
measure bell259
cnot bell259 bell258
cnot bell258 c8
cnot bell256 c8
H bell256
measure bell256
cz bell256 b2
T* c8
H bell260
cnot bell260 bell261
cnot b3 bell261
measure bell261
cnot bell261 bell260
cnot bell260 c8
T c8
cnot bell258 c8
H bell258
measure bell258
cz bell258 a5
T* c8
H bell262
cnot bell262 bell263
cnot a4 bell263
measure bell263
cnot bell263 bell262
cnot bell262 c8
cnot bell260 c8
H bell260
measure bell260
cz bell260 b3
T* c8
H bell264
cnot bell264 bell265
cnot b4 bell265
measure bell265
cnot bell265 bell264
cnot bell264 c8
T c8
cnot bell262 c8
H bell262
measure bell262
cz bell262 a4
T* c8
H bell266
cnot bell266 bell267
cnot a3 bell267
measure bell267
cnot bell267 bell266
cnot bell266 c8
cnot bell264 c8
H bell264
measure bell264
cz bell264 b4
T* c8
H bell268
cnot bell268 bell269
cnot b5 bell269
measure bell269
cnot bell269 bell268
cnot bell268 c8
T c8
cnot bell266 c8
H bell266
measure bell266
cz bell266 a3
T* c8
H bell270
cnot bell270 bell271
cnot a2 bell271
measure bell271
cnot bell271 bell270
cnot bell270 c8
cnot bell268 c8
H bell268
measure bell268
cz bell268 b5
T* c8
H bell272
cnot bell272 bell273
cnot b6 bell273
measure bell273
cnot bell273 bell272
cnot bell272 c8
T c8
cnot bell270 c8
H bell270
measure bell270
cz bell270 a2
T* c8
H bell274
cnot bell274 bell275
cnot a1 bell275
measure bell275
cnot bell275 bell274
cnot bell274 c8
cnot bell272 c8
H bell272
measure bell272
cz bell272 b6
T* c8
H bell276
cnot bell276 bell277
cnot b7 bell277
measure bell277
cnot bell277 bell276
cnot bell276 c8
T c8
cnot bell274 c8
H bell274
measure bell274
cz bell274 a1
T* c8
H bell278
cnot bell278 bell279
cnot a0 bell279
measure bell279
cnot bell279 bell278
cnot bell278 c8
cnot bell276 c8
H bell276
measure bell276
cz bell276 b7
T* c8
H bell280
cnot bell280 bell281
cnot b8 bell281
measure bell281
cnot bell281 bell280
cnot bell280 c8
T c8
cnot bell278 c8
H bell278
measure bell278
cz bell278 a0
T* c8
cnot bell280 c8
H bell280
measure bell280
cz bell280 b8
H c8
S c9
H bell282
cnot bell282 bell283
cnot a9 bell283
measure bell283
cnot bell283 bell282
cnot bell282 c9
T* c9
cnot b0 c9
T c9
cnot bell282 c9
H bell282
measure bell282
cz bell282 a9
T* c9
H bell284
cnot bell284 bell285
cnot a8 bell285
measure bell285
cnot bell285 bell284
cnot bell284 c9
cnot b0 c9
T* c9
H bell286
cnot bell286 bell287
cnot b1 bell287
measure bell287
cnot bell287 bell286
cnot bell286 c9
T c9
cnot bell284 c9
H bell284
measure bell284
cz bell284 a8
T* c9
H bell288
cnot bell288 bell289
cnot a7 bell289
measure bell289
cnot bell289 bell288
cnot bell288 c9
cnot bell286 c9
H bell286
measure bell286
cz bell286 b1
T* c9
H bell290
cnot bell290 bell291
cnot b2 bell291
measure bell291
cnot bell291 bell290
cnot bell290 c9
T c9
cnot bell288 c9
H bell288
measure bell288
cz bell288 a7
T* c9
H bell292
cnot bell292 bell293
cnot a6 bell293
measure bell293
cnot bell293 bell292
cnot bell292 c9
cnot bell290 c9
H bell290
measure bell290
cz bell290 b2
T* c9
H bell294
cnot bell294 bell295
cnot b3 bell295
measure bell295
cnot bell295 bell294
cnot bell294 c9
T c9
cnot bell292 c9
H bell292
measure bell292
cz bell292 a6
T* c9
H bell296
cnot bell296 bell297
cnot a5 bell297
measure bell297
cnot bell297 bell296
cnot bell296 c9
cnot bell294 c9
H bell294
measure bell294
cz bell294 b3
T* c9
H bell298
cnot bell298 bell299
cnot b4 bell299
measure bell299
cnot bell299 bell298
cnot bell298 c9
T c9
cnot bell296 c9
H bell296
measure bell296
cz bell296 a5
T* c9
H bell300
cnot bell300 bell301
cnot a4 bell301
measure bell301
cnot bell301 bell300
cnot bell300 c9
cnot bell298 c9
H bell298
measure bell298
cz bell298 b4
T* c9
H bell302
cnot bell302 bell303
cnot b5 bell303
measure bell303
cnot bell303 bell302
cnot bell302 c9
T c9
cnot bell300 c9
H bell300
measure bell300
cz bell300 a4
T* c9
H bell304
cnot bell304 bell305
cnot a3 bell305
measure bell305
cnot bell305 bell304
cnot bell304 c9
cnot bell302 c9
H bell302
measure bell302
cz bell302 b5
T* c9
H bell306
cnot bell306 bell307
cnot b6 bell307
measure bell307
cnot bell307 bell306
cnot bell306 c9
T c9
cnot bell304 c9
H bell304
measure bell304
cz bell304 a3
T* c9
H bell308
cnot bell308 bell309
cnot a2 bell309
measure bell309
cnot bell309 bell308
cnot bell308 c9
cnot bell306 c9
H bell306
measure bell306
cz bell306 b6
T* c9
H bell310
cnot bell310 bell311
cnot b7 bell311
measure bell311
cnot bell311 bell310
cnot bell310 c9
T c9
cnot bell308 c9
H bell308
measure bell308
cz bell308 a2
T* c9
H bell312
cnot bell312 bell313
cnot a1 bell313
measure bell313
cnot bell313 bell312
cnot bell312 c9
cnot bell310 c9
H bell310
measure bell310
cz bell310 b7
T* c9
H bell314
cnot bell314 bell315
cnot b8 bell315
measure bell315
cnot bell315 bell314
cnot bell314 c9
T c9
cnot bell312 c9
H bell312
measure bell312
cz bell312 a1
T* c9
cnot a0 c9
cnot bell314 c9
H bell314
measure bell314
cz bell314 b8
T* c9
H bell316
cnot bell316 bell317
cnot b9 bell317
measure bell317
cnot bell317 bell316
cnot bell316 c9
T c9
cnot a0 c9
T* c9
cnot bell316 c9
H bell316
measure bell316
cz bell316 b9
H c9
S a0
S a1
S b0
cnot a0 b0
T* b0
H bell318
cnot bell318 bell319
cnot a1 bell319
measure bell319
cnot bell319 bell318
cnot bell318 b0
H bell318
measure bell318
cz bell318 a1
cnot a0 b0
T* b0
S b1
H bell320
cnot bell320 bell321
cnot a0 bell321
measure bell321
cnot bell321 bell320
cnot bell320 b1
T* b1
cnot a1 b1
cnot bell320 b1
T* b1
S a2
H bell322
cnot bell322 bell323
cnot b0 bell323
measure bell323
cnot bell323 bell322
cnot bell322 a2
H bell324
cnot bell324 bell325
cnot a1 bell325
measure bell325
cnot bell325 bell324
cnot bell324 a2
T* a2
H bell326
cnot bell326 bell327
cnot b1 bell327
measure bell327
cnot bell327 bell326
cnot bell326 a2
cnot bell322 a2
T* a2
S b2
cnot bell320 b2
T* b2
cnot a1 b2
cnot bell320 b2
H bell320
measure bell320
cz bell320 a0
T* b2
cnot b1 b2
H bell328
cnot bell328 bell329
cnot a2 bell329
measure bell329
cnot bell329 bell328
cnot bell328 b2
H bell328
measure bell328
cz bell328 a2
T* b2
S a3
cnot bell322 a3
cnot bell324 a3
T* a3
cnot bell326 a3
cnot bell322 a3
H bell322
measure bell322
cz bell322 b0
T* a3
H bell330
cnot bell330 bell331
cnot b2 bell331
measure bell331
cnot bell331 bell330
cnot bell330 a3
cnot a2 a3
T* a3
S b3
H bell332
cnot bell332 bell333
cnot a0 bell333
measure bell333
cnot bell333 bell332
cnot bell332 b3
T* b3
cnot bell324 b3
H bell324
measure bell324
cz bell324 a1
cnot bell332 b3
H bell332
measure bell332
cz bell332 a0
T* b3
cnot bell326 b3
H bell326
measure bell326
cz bell326 b1
cnot a2 b3
T* b3
cnot bell330 b3
H bell330
measure bell330
cz bell330 b2
cnot a3 b3
T* b3
S a4
H bell334
cnot bell334 bell335
cnot b0 bell335
measure bell335
cnot bell335 bell334
cnot bell334 a4
H bell336
cnot bell336 bell337
cnot a1 bell337
measure bell337
cnot bell337 bell336
cnot bell336 a4
T* a4
H bell338
cnot bell338 bell339
cnot b1 bell339
measure bell339
cnot bell339 bell338
cnot bell338 a4
cnot bell334 a4
T* a4
H bell340
cnot bell340 bell341
cnot b2 bell341
measure bell341
cnot bell341 bell340
cnot bell340 a4
H bell342
cnot bell342 bell343
cnot a2 bell343
measure bell343
cnot bell343 bell342
cnot bell342 a4
T* a4
H bell344
cnot bell344 bell345
cnot b3 bell345
measure bell345
cnot bell345 bell344
cnot bell344 a4
H bell346
cnot bell346 bell347
cnot a3 bell347
measure bell347
cnot bell347 bell346
cnot bell346 a4
T* a4
S b4
H bell348
cnot bell348 bell349
cnot a0 bell349
measure bell349
cnot bell349 bell348
cnot bell348 b4
T* b4
cnot bell336 b4
cnot bell348 b4
H bell348
measure bell348
cz bell348 a0
T* b4
cnot bell338 b4
cnot bell342 b4
T* b4
cnot bell340 b4
cnot bell346 b4
T* b4
cnot bell344 b4
cnot a4 b4
T* b4
S a5
cnot bell334 a5
cnot bell336 a5
H bell336
measure bell336
cz bell336 a1
T* a5
cnot bell338 a5
H bell338
measure bell338
cz bell338 b1
cnot bell334 a5
T* a5
cnot bell340 a5
H bell340
measure bell340
cz bell340 b2
cnot bell342 a5
H bell342
measure bell342
cz bell342 a2
T* a5
cnot bell344 a5
H bell344
measure bell344
cz bell344 b3
cnot bell346 a5
H bell346
measure bell346
cz bell346 a3
T* a5
cnot b4 a5
cnot a4 a5
T* a5
S b5
H bell350
cnot bell350 bell351
cnot a0 bell351
measure bell351
cnot bell351 bell350
cnot bell350 b5
T* b5
H bell352
cnot bell352 bell353
cnot a1 bell353
measure bell353
cnot bell353 bell352
cnot bell352 b5
H bell352
measure bell352
cz bell352 a1
cnot bell350 b5
H bell350
measure bell350
cz bell350 a0
T* b5
H bell354
cnot bell354 bell355
cnot b1 bell355
measure bell355
cnot bell355 bell354
cnot bell354 b5
H bell354
measure bell354
cz bell354 b1
H bell356
cnot bell356 bell357
cnot a2 bell357
measure bell357
cnot bell357 bell356
cnot bell356 b5
H bell356
measure bell356
cz bell356 a2
T* b5
H bell358
cnot bell358 bell359
cnot b2 bell359
measure bell359
cnot bell359 bell358
cnot bell358 b5
H bell358
measure bell358
cz bell358 b2
H bell360
cnot bell360 bell361
cnot a3 bell361
measure bell361
cnot bell361 bell360
cnot bell360 b5
H bell360
measure bell360
cz bell360 a3
T* b5
H bell362
cnot bell362 bell363
cnot b3 bell363
measure bell363
cnot bell363 bell362
cnot bell362 b5
H bell362
measure bell362
cz bell362 b3
H bell364
cnot bell364 bell365
cnot a4 bell365
measure bell365
cnot bell365 bell364
cnot bell364 b5
H bell364
measure bell364
cz bell364 a4
T* b5
H bell366
cnot bell366 bell367
cnot b4 bell367
measure bell367
cnot bell367 bell366
cnot bell366 b5
H bell366
measure bell366
cz bell366 b4
H bell368
cnot bell368 bell369
cnot a5 bell369
measure bell369
cnot bell369 bell368
cnot bell368 b5
H bell368
measure bell368
cz bell368 a5
T* b5
S a6
cnot bell334 a6
H bell370
cnot bell370 bell371
cnot a1 bell371
measure bell371
cnot bell371 bell370
cnot bell370 a6
H bell370
measure bell370
cz bell370 a1
T* a6
H bell372
cnot bell372 bell373
cnot b1 bell373
measure bell373
cnot bell373 bell372
cnot bell372 a6
H bell372
measure bell372
cz bell372 b1
cnot bell334 a6
H bell334
measure bell334
cz bell334 b0
T* a6
H bell374
cnot bell374 bell375
cnot b2 bell375
measure bell375
cnot bell375 bell374
cnot bell374 a6
H bell374
measure bell374
cz bell374 b2
H bell376
cnot bell376 bell377
cnot a2 bell377
measure bell377
cnot bell377 bell376
cnot bell376 a6
H bell376
measure bell376
cz bell376 a2
T* a6
H bell378
cnot bell378 bell379
cnot b3 bell379
measure bell379
cnot bell379 bell378
cnot bell378 a6
H bell378
measure bell378
cz bell378 b3
H bell380
cnot bell380 bell381
cnot a3 bell381
measure bell381
cnot bell381 bell380
cnot bell380 a6
H bell380
measure bell380
cz bell380 a3
T* a6
cnot b4 a6
cnot a4 a6
T* a6
H bell382
cnot bell382 bell383
cnot b5 bell383
measure bell383
cnot bell383 bell382
cnot bell382 a6
H bell382
measure bell382
cz bell382 b5
cnot a5 a6
T* a6
S b6
H bell384
cnot bell384 bell385
cnot a0 bell385
measure bell385
cnot bell385 bell384
cnot bell384 b6
T* b6
H bell386
cnot bell386 bell387
cnot a1 bell387
measure bell387
cnot bell387 bell386
cnot bell386 b6
cnot bell384 b6
T* b6
H bell388
cnot bell388 bell389
cnot b1 bell389
measure bell389
cnot bell389 bell388
cnot bell388 b6
H bell390
cnot bell390 bell391
cnot a2 bell391
measure bell391
cnot bell391 bell390
cnot bell390 b6
T* b6
H bell392
cnot bell392 bell393
cnot b2 bell393
measure bell393
cnot bell393 bell392
cnot bell392 b6
H bell394
cnot bell394 bell395
cnot a3 bell395
measure bell395
cnot bell395 bell394
cnot bell394 b6
T* b6
H bell396
cnot bell396 bell397
cnot b3 bell397
measure bell397
cnot bell397 bell396
cnot bell396 b6
H bell398
cnot bell398 bell399
cnot a4 bell399
measure bell399
cnot bell399 bell398
cnot bell398 b6
T* b6
H bell400
cnot bell400 bell401
cnot b4 bell401
measure bell401
cnot bell401 bell400
cnot bell400 b6
H bell402
cnot bell402 bell403
cnot a5 bell403
measure bell403
cnot bell403 bell402
cnot bell402 b6
T* b6
H bell404
cnot bell404 bell405
cnot b5 bell405
measure bell405
cnot bell405 bell404
cnot bell404 b6
H bell406
cnot bell406 bell407
cnot a6 bell407
measure bell407
cnot bell407 bell406
cnot bell406 b6
T* b6
S a7
H bell408
cnot bell408 bell409
cnot b0 bell409
measure bell409
cnot bell409 bell408
cnot bell408 a7
cnot bell386 a7
T* a7
cnot bell388 a7
cnot bell408 a7
T* a7
cnot bell392 a7
cnot bell390 a7
T* a7
cnot bell396 a7
cnot bell394 a7
T* a7
cnot bell400 a7
cnot bell398 a7
T* a7
cnot bell404 a7
cnot bell402 a7
T* a7
cnot b6 a7
cnot bell406 a7
T* a7
S b7
cnot bell384 b7
T* b7
cnot bell386 b7
cnot bell384 b7
H bell384
measure bell384
cz bell384 a0
T* b7
cnot bell388 b7
cnot bell390 b7
T* b7
cnot bell392 b7
cnot bell394 b7
T* b7
cnot bell396 b7
cnot bell398 b7
T* b7
cnot bell400 b7
cnot bell402 b7
T* b7
cnot bell404 b7
cnot bell406 b7
T* b7
cnot b6 b7
cnot a7 b7
T* b7
S a8
cnot bell408 a8
cnot bell386 a8
H bell386
measure bell386
cz bell386 a1
T* a8
cnot bell388 a8
H bell388
measure bell388
cz bell388 b1
cnot bell408 a8
H bell408
measure bell408
cz bell408 b0
T* a8
cnot bell392 a8
H bell392
measure bell392
cz bell392 b2
cnot bell390 a8
H bell390
measure bell390
cz bell390 a2
T* a8
cnot bell396 a8
H bell396
measure bell396
cz bell396 b3
cnot bell394 a8
H bell394
measure bell394
cz bell394 a3
T* a8
cnot bell400 a8
H bell400
measure bell400
cz bell400 b4
cnot bell398 a8
H bell398
measure bell398
cz bell398 a4
T* a8
cnot bell404 a8
H bell404
measure bell404
cz bell404 b5
cnot bell402 a8
H bell402
measure bell402
cz bell402 a5
T* a8
cnot b6 a8
cnot bell406 a8
H bell406
measure bell406
cz bell406 a6
T* a8
cnot b7 a8
cnot a7 a8
T* a8
S b8
H bell410
cnot bell410 bell411
cnot a0 bell411
measure bell411
cnot bell411 bell410
cnot bell410 b8
T* b8
H bell412
cnot bell412 bell413
cnot a1 bell413
measure bell413
cnot bell413 bell412
cnot bell412 b8
cnot bell410 b8
T* b8
H bell414
cnot bell414 bell415
cnot b1 bell415
measure bell415
cnot bell415 bell414
cnot bell414 b8
H bell416
cnot bell416 bell417
cnot a2 bell417
measure bell417
cnot bell417 bell416
cnot bell416 b8
T* b8
H bell418
cnot bell418 bell419
cnot b2 bell419
measure bell419
cnot bell419 bell418
cnot bell418 b8
H bell420
cnot bell420 bell421
cnot a3 bell421
measure bell421
cnot bell421 bell420
cnot bell420 b8
T* b8
H bell422
cnot bell422 bell423
cnot b3 bell423
measure bell423
cnot bell423 bell422
cnot bell422 b8
H bell424
cnot bell424 bell425
cnot a4 bell425
measure bell425
cnot bell425 bell424
cnot bell424 b8
T* b8
H bell426
cnot bell426 bell427
cnot b4 bell427
measure bell427
cnot bell427 bell426
cnot bell426 b8
H bell428
cnot bell428 bell429
cnot a5 bell429
measure bell429
cnot bell429 bell428
cnot bell428 b8
T* b8
cnot b5 b8
H bell430
cnot bell430 bell431
cnot a6 bell431
measure bell431
cnot bell431 bell430
cnot bell430 b8
T* b8
H bell432
cnot bell432 bell433
cnot b6 bell433
measure bell433
cnot bell433 bell432
cnot bell432 b8
H bell434
cnot bell434 bell435
cnot a7 bell435
measure bell435
cnot bell435 bell434
cnot bell434 b8
T* b8
H bell436
cnot bell436 bell437
cnot b7 bell437
measure bell437
cnot bell437 bell436
cnot bell436 b8
H bell438
cnot bell438 bell439
cnot a8 bell439
measure bell439
cnot bell439 bell438
cnot bell438 b8
T* b8
S a9
H bell440
cnot bell440 bell441
cnot b0 bell441
measure bell441
cnot bell441 bell440
cnot bell440 a9
cnot bell412 a9
T* a9
cnot bell414 a9
cnot bell440 a9
H bell440
measure bell440
cz bell440 b0
T* a9
cnot bell418 a9
cnot bell416 a9
T* a9
cnot bell422 a9
cnot bell420 a9
T* a9
cnot bell426 a9
cnot bell424 a9
T* a9
cnot b5 a9
cnot bell428 a9
T* a9
cnot bell432 a9
cnot bell430 a9
T* a9
cnot bell436 a9
cnot bell434 a9
T* a9
cnot b8 a9
cnot bell438 a9
T* a9
S b9
cnot bell410 b9
T* b9
cnot bell412 b9
H bell412
measure bell412
cz bell412 a1
cnot bell410 b9
H bell410
measure bell410
cz bell410 a0
T* b9
cnot bell414 b9
H bell414
measure bell414
cz bell414 b1
cnot bell416 b9
H bell416
measure bell416
cz bell416 a2
T* b9
cnot bell418 b9
H bell418
measure bell418
cz bell418 b2
cnot bell420 b9
H bell420
measure bell420
cz bell420 a3
T* b9
cnot bell422 b9
H bell422
measure bell422
cz bell422 b3
cnot bell424 b9
H bell424
measure bell424
cz bell424 a4
T* b9
cnot bell426 b9
H bell426
measure bell426
cz bell426 b4
cnot bell428 b9
H bell428
measure bell428
cz bell428 a5
T* b9
cnot b5 b9
cnot bell430 b9
H bell430
measure bell430
cz bell430 a6
T* b9
cnot bell432 b9
H bell432
measure bell432
cz bell432 b6
cnot bell434 b9
H bell434
measure bell434
cz bell434 a7
T* b9
cnot bell436 b9
H bell436
measure bell436
cz bell436 b7
cnot bell438 b9
H bell438
measure bell438
cz bell438 a8
T* b9
cnot b8 b9
cnot a9 b9
T* b9
H bell442
cnot bell442 bell443
cnot b1 bell443
measure bell443
cnot bell443 bell442
cnot bell442 a2
H bell442
measure bell442
cz bell442 b1
H bell444
cnot bell444 bell445
cnot b2 bell445
measure bell445
cnot bell445 bell444
cnot bell444 a3
H bell444
measure bell444
cz bell444 b2
H bell446
cnot bell446 bell447
cnot b3 bell447
measure bell447
cnot bell447 bell446
cnot bell446 a4
H bell446
measure bell446
cz bell446 b3
cnot b4 a5
H bell448
cnot bell448 bell449
cnot b5 bell449
measure bell449
cnot bell449 bell448
cnot bell448 a6
H bell448
measure bell448
cz bell448 b5
cnot b6 a7
cnot b7 a8
cnot b8 a9
cnot a9 b9
cnot a7 a8
H bell450
cnot bell450 bell451
cnot a6 bell451
measure bell451
cnot bell451 bell450
cnot bell450 a8
cnot bell450 a7
H bell452
cnot bell452 bell453
cnot a8 bell453
measure bell453
cnot bell453 bell452
cnot bell452 b9
cnot bell452 b8
cnot a7 b7
cnot bell450 b6
H bell450
measure bell450
cz bell450 a6
cnot bell452 a9
H bell452
measure bell452
cz bell452 a8
cnot a4 a5
H bell454
cnot bell454 bell455
cnot a3 bell455
measure bell455
cnot bell455 bell454
cnot bell454 a5
cnot bell454 a4
H bell454
measure bell454
cz bell454 a3
H bell456
cnot bell456 bell457
cnot a5 bell457
measure bell457
cnot bell457 bell456
cnot bell456 b9
cnot bell456 b8
H bell456
measure bell456
cz bell456 a5
H bell458
cnot bell458 bell459
cnot a5 bell459
measure bell459
cnot bell459 bell458
cnot bell458 b7
cnot bell458 b6
H bell458
measure bell458
cz bell458 a5
H bell460
cnot bell460 bell461
cnot a5 bell461
measure bell461
cnot bell461 bell460
cnot bell460 b5
cnot a4 b4
cnot a3 b3
cnot bell460 a9
H bell460
measure bell460
cz bell460 a5
H bell462
cnot bell462 bell463
cnot a5 bell463
measure bell463
cnot bell463 bell462
cnot bell462 a8
cnot bell462 a7
H bell462
measure bell462
cz bell462 a5
cnot a5 a6
H bell464
cnot bell464 bell465
cnot a1 bell465
measure bell465
cnot bell465 bell464
cnot bell464 a2
H bell464
measure bell464
cz bell464 a1
H bell466
cnot bell466 bell467
cnot a2 bell467
measure bell467
cnot bell467 bell466
cnot bell466 b9
cnot bell466 b8
H bell466
measure bell466
cz bell466 a2
H bell468
cnot bell468 bell469
cnot a2 bell469
measure bell469
cnot bell469 bell468
cnot bell468 b7
cnot bell468 b6
H bell468
measure bell468
cz bell468 a2
H bell470
cnot bell470 bell471
cnot a2 bell471
measure bell471
cnot bell471 bell470
cnot bell470 b5
H bell470
measure bell470
cz bell470 a2
H bell472
cnot bell472 bell473
cnot a2 bell473
measure bell473
cnot bell473 bell472
cnot bell472 b4
H bell472
measure bell472
cz bell472 a2
cnot a2 b3
H bell474
cnot bell474 bell475
cnot a2 bell475
measure bell475
cnot bell475 bell474
cnot bell474 b2
H bell474
measure bell474
cz bell474 a2
cnot a1 b1
H bell476
cnot bell476 bell477
cnot a1 bell477
measure bell477
cnot bell477 bell476
cnot bell476 b0
H bell476
measure bell476
cz bell476 a1
H bell478
cnot bell478 bell479
cnot a2 bell479
measure bell479
cnot bell479 bell478
cnot bell478 a9
H bell478
measure bell478
cz bell478 a2
H bell480
cnot bell480 bell481
cnot a2 bell481
measure bell481
cnot bell481 bell480
cnot bell480 a8
cnot bell480 a7
H bell480
measure bell480
cz bell480 a2
H bell482
cnot bell482 bell483
cnot a2 bell483
measure bell483
cnot bell483 bell482
cnot bell482 a6
cnot bell482 a5
cnot bell482 a4
H bell482
measure bell482
cz bell482 a2
cnot a2 a3
reset bell0
reset bell1
reset bell2
reset bell3
reset bell4
reset bell5
reset bell6
reset bell7
reset bell8
reset bell9
reset bell10
reset bell11
reset bell12
reset bell13
reset bell14
reset bell15
reset bell16
reset bell17
reset bell18
reset bell19
reset bell20
reset bell21
reset bell22
reset bell23
reset bell24
reset bell25
reset bell26
reset bell27
reset bell28
reset bell29
reset bell30
reset bell31
reset bell32
reset bell33
reset bell34
reset bell35
reset bell36
reset bell37
reset bell38
reset bell39
reset bell40
reset bell41
reset bell42
reset bell43
reset bell44
reset bell45
reset bell46
reset bell47
reset bell48
reset bell49
reset bell50
reset bell51
reset bell52
reset bell53
reset bell54
reset bell55
reset bell56
reset bell57
reset bell58
reset bell59
reset bell60
reset bell61
reset bell62
reset bell63
reset bell64
reset bell65
reset bell66
reset bell67
reset bell68
reset bell69
reset bell70
reset bell71
reset bell72
reset bell73
reset bell74
reset bell75
reset bell76
reset bell77
reset bell78
reset bell79
reset bell80
reset bell81
reset bell82
reset bell83
reset bell84
reset bell85
reset bell86
reset bell87
reset bell88
reset bell89
reset bell90
reset bell91
reset bell92
reset bell93
reset bell94
reset bell95
reset bell96
reset bell97
reset bell98
reset bell99
reset bell100
reset bell101
reset bell102
reset bell103
reset bell104
reset bell105
reset bell106
reset bell107
reset bell108
reset bell109
reset bell110
reset bell111
reset bell112
reset bell113
reset bell114
reset bell115
reset bell116
reset bell117
reset bell118
reset bell119
reset bell120
reset bell121
reset bell122
reset bell123
reset bell124
reset bell125
reset bell126
reset bell127
reset bell128
reset bell129
reset bell130
reset bell131
reset bell132
reset bell133
reset bell134
reset bell135
reset bell136
reset bell137
reset bell138
reset bell139
reset bell140
reset bell141
reset bell142
reset bell143
reset bell144
reset bell145
reset bell146
reset bell147
reset bell148
reset bell149
reset bell150
reset bell151
reset bell152
reset bell153
reset bell154
reset bell155
reset bell156
reset bell157
reset bell158
reset bell159
reset bell160
reset bell161
reset bell162
reset bell163
reset bell164
reset bell165
reset bell166
reset bell167
reset bell168
reset bell169
reset bell170
reset bell171
reset bell172
reset bell173
reset bell174
reset bell175
reset bell176
reset bell177
reset bell178
reset bell179
reset bell180
reset bell181
reset bell182
reset bell183
reset bell184
reset bell185
reset bell186
reset bell187
reset bell188
reset bell189
reset bell190
reset bell191
reset bell192
reset bell193
reset bell194
reset bell195
reset bell196
reset bell197
reset bell198
reset bell199
reset bell200
reset bell201
reset bell202
reset bell203
reset bell204
reset bell205
reset bell206
reset bell207
reset bell208
reset bell209
reset bell210
reset bell211
reset bell212
reset bell213
reset bell214
reset bell215
reset bell216
reset bell217
reset bell218
reset bell219
reset bell220
reset bell221
reset bell222
reset bell223
reset bell224
reset bell225
reset bell226
reset bell227
reset bell228
reset bell229
reset bell230
reset bell231
reset bell232
reset bell233
reset bell234
reset bell235
reset bell236
reset bell237
reset bell238
reset bell239
reset bell240
reset bell241
reset bell242
reset bell243
reset bell244
reset bell245
reset bell246
reset bell247
reset bell248
reset bell249
reset bell250
reset bell251
reset bell252
reset bell253
reset bell254
reset bell255
reset bell256
reset bell257
reset bell258
reset bell259
reset bell260
reset bell261
reset bell262
reset bell263
reset bell264
reset bell265
reset bell266
reset bell267
reset bell268
reset bell269
reset bell270
reset bell271
reset bell272
reset bell273
reset bell274
reset bell275
reset bell276
reset bell277
reset bell278
reset bell279
reset bell280
reset bell281
reset bell282
reset bell283
reset bell284
reset bell285
reset bell286
reset bell287
reset bell288
reset bell289
reset bell290
reset bell291
reset bell292
reset bell293
reset bell294
reset bell295
reset bell296
reset bell297
reset bell298
reset bell299
reset bell300
reset bell301
reset bell302
reset bell303
reset bell304
reset bell305
reset bell306
reset bell307
reset bell308
reset bell309
reset bell310
reset bell311
reset bell312
reset bell313
reset bell314
reset bell315
reset bell316
reset bell317
reset bell318
reset bell319
reset bell320
reset bell321
reset bell322
reset bell323
reset bell324
reset bell325
reset bell326
reset bell327
reset bell328
reset bell329
reset bell330
reset bell331
reset bell332
reset bell333
reset bell334
reset bell335
reset bell336
reset bell337
reset bell338
reset bell339
reset bell340
reset bell341
reset bell342
reset bell343
reset bell344
reset bell345
reset bell346
reset bell347
reset bell348
reset bell349
reset bell350
reset bell351
reset bell352
reset bell353
reset bell354
reset bell355
reset bell356
reset bell357
reset bell358
reset bell359
reset bell360
reset bell361
reset bell362
reset bell363
reset bell364
reset bell365
reset bell366
reset bell367
reset bell368
reset bell369
reset bell370
reset bell371
reset bell372
reset bell373
reset bell374
reset bell375
reset bell376
reset bell377
reset bell378
reset bell379
reset bell380
reset bell381
reset bell382
reset bell383
reset bell384
reset bell385
reset bell386
reset bell387
reset bell388
reset bell389
reset bell390
reset bell391
reset bell392
reset bell393
reset bell394
reset bell395
reset bell396
reset bell397
reset bell398
reset bell399
reset bell400
reset bell401
reset bell402
reset bell403
reset bell404
reset bell405
reset bell406
reset bell407
reset bell408
reset bell409
reset bell410
reset bell411
reset bell412
reset bell413
reset bell414
reset bell415
reset bell416
reset bell417
reset bell418
reset bell419
reset bell420
reset bell421
reset bell422
reset bell423
reset bell424
reset bell425
reset bell426
reset bell427
reset bell428
reset bell429
reset bell430
reset bell431
reset bell432
reset bell433
reset bell434
reset bell435
reset bell436
reset bell437
reset bell438
reset bell439
reset bell440
reset bell441
reset bell442
reset bell443
reset bell444
reset bell445
reset bell446
reset bell447
reset bell448
reset bell449
reset bell450
reset bell451
reset bell452
reset bell453
reset bell454
reset bell455
reset bell456
reset bell457
reset bell458
reset bell459
reset bell460
reset bell461
reset bell462
reset bell463
reset bell464
reset bell465
reset bell466
reset bell467
reset bell468
reset bell469
reset bell470
reset bell471
reset bell472
reset bell473
reset bell474
reset bell475
reset bell476
reset bell477
reset bell478
reset bell479
reset bell480
reset bell481
reset bell482
reset bell483
END
