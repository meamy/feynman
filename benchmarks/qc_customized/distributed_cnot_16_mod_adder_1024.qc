# Hyperedge cut (ebits): 133

# Actual ebits used (Synthesis): 254
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/mod_adder_1024.qc):
#   Qubits: 28
#   H: 570
#   T: 1995
#   cnot: 1720
#   Depth: 2218
#   T depth: 981
# Result (786.496ms):
#   Qubits: 536
#   H: 838
#   T: 1259
#   cnot: 2000
#   cz: 254
#   measure: 508
#   reset: 508
#   swap: 8
#   Depth: 2875
#   T depth: 864


# Result Circuit
.v x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 0 1 2 3 4 5 6 7 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell180 bell181 bell182 bell183 bell184 bell185 bell186 bell187 bell188 bell189 bell19 bell190 bell191 bell192 bell193 bell194 bell195 bell196 bell197 bell198 bell199 bell2 bell20 bell200 bell201 bell202 bell203 bell204 bell205 bell206 bell207 bell208 bell209 bell21 bell210 bell211 bell212 bell213 bell214 bell215 bell216 bell217 bell218 bell219 bell22 bell220 bell221 bell222 bell223 bell224 bell225 bell226 bell227 bell228 bell229 bell23 bell230 bell231 bell232 bell233 bell234 bell235 bell236 bell237 bell238 bell239 bell24 bell240 bell241 bell242 bell243 bell244 bell245 bell246 bell247 bell248 bell249 bell25 bell250 bell251 bell252 bell253 bell254 bell255 bell256 bell257 bell258 bell259 bell26 bell260 bell261 bell262 bell263 bell264 bell265 bell266 bell267 bell268 bell269 bell27 bell270 bell271 bell272 bell273 bell274 bell275 bell276 bell277 bell278 bell279 bell28 bell280 bell281 bell282 bell283 bell284 bell285 bell286 bell287 bell288 bell289 bell29 bell290 bell291 bell292 bell293 bell294 bell295 bell296 bell297 bell298 bell299 bell3 bell30 bell300 bell301 bell302 bell303 bell304 bell305 bell306 bell307 bell308 bell309 bell31 bell310 bell311 bell312 bell313 bell314 bell315 bell316 bell317 bell318 bell319 bell32 bell320 bell321 bell322 bell323 bell324 bell325 bell326 bell327 bell328 bell329 bell33 bell330 bell331 bell332 bell333 bell334 bell335 bell336 bell337 bell338 bell339 bell34 bell340 bell341 bell342 bell343 bell344 bell345 bell346 bell347 bell348 bell349 bell35 bell350 bell351 bell352 bell353 bell354 bell355 bell356 bell357 bell358 bell359 bell36 bell360 bell361 bell362 bell363 bell364 bell365 bell366 bell367 bell368 bell369 bell37 bell370 bell371 bell372 bell373 bell374 bell375 bell376 bell377 bell378 bell379 bell38 bell380 bell381 bell382 bell383 bell384 bell385 bell386 bell387 bell388 bell389 bell39 bell390 bell391 bell392 bell393 bell394 bell395 bell396 bell397 bell398 bell399 bell4 bell40 bell400 bell401 bell402 bell403 bell404 bell405 bell406 bell407 bell408 bell409 bell41 bell410 bell411 bell412 bell413 bell414 bell415 bell416 bell417 bell418 bell419 bell42 bell420 bell421 bell422 bell423 bell424 bell425 bell426 bell427 bell428 bell429 bell43 bell430 bell431 bell432 bell433 bell434 bell435 bell436 bell437 bell438 bell439 bell44 bell440 bell441 bell442 bell443 bell444 bell445 bell446 bell447 bell448 bell449 bell45 bell450 bell451 bell452 bell453 bell454 bell455 bell456 bell457 bell458 bell459 bell46 bell460 bell461 bell462 bell463 bell464 bell465 bell466 bell467 bell468 bell469 bell47 bell470 bell471 bell472 bell473 bell474 bell475 bell476 bell477 bell478 bell479 bell48 bell480 bell481 bell482 bell483 bell484 bell485 bell486 bell487 bell488 bell489 bell49 bell490 bell491 bell492 bell493 bell494 bell495 bell496 bell497 bell498 bell499 bell5 bell50 bell500 bell501 bell502 bell503 bell504 bell505 bell506 bell507 bell51 bell52 bell53 bell54 bell55 bell56 bell57 bell58 bell59 bell6 bell60 bell61 bell62 bell63 bell64 bell65 bell66 bell67 bell68 bell69 bell7 bell70 bell71 bell72 bell73 bell74 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
.i x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
.o x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
BEGIN 
H bell0
cnot bell0 bell1
cnot x10 bell1
measure bell1
cnot bell1 bell0
cnot bell0 x20
H bell0
measure bell0
cz bell0 x10
H x20
T x20
cnot x19 x20
T* x20
H bell2
cnot bell2 bell3
cnot x9 bell3
measure bell3
cnot bell3 bell2
cnot bell2 x20
T x20
cnot x19 x20
T* x20
cnot bell2 x20
swap 0 1
cnot bell2 x19
H 0
T 0
H bell4
cnot bell4 bell5
cnot x18 bell5
measure bell5
cnot bell5 bell4
cnot bell4 0
T* 0
H bell6
cnot bell6 bell7
cnot x8 bell7
measure bell7
cnot bell7 bell6
cnot bell6 0
T 0
cnot bell4 0
T* 0
cnot bell6 0
H 0
T x20
H bell8
cnot bell8 bell9
cnot 0 bell9
measure bell9
cnot bell9 bell8
cnot bell8 x20
T* x20
cnot x19 x20
T x20
cnot bell8 x20
H bell8
measure bell8
cz bell8 0
T* x20
cnot x19 x20
T 0
H bell10
cnot bell10 bell11
cnot x19 bell11
measure bell11
cnot bell11 bell10
cnot bell10 0
T* 0
cnot bell10 0
H bell10
measure bell10
cz bell10 x19
H 0
T* 0
cnot bell4 0
T 0
cnot bell6 0
T* 0
cnot bell4 0
H bell4
measure bell4
cz bell4 x18
T 0
cnot bell6 0
H bell6
measure bell6
cz bell6 x8
cnot bell2 x19
T x19
cnot bell2 x19
H bell2
measure bell2
cz bell2 x9
H x19
T x19
H bell12
cnot bell12 bell13
cnot x18 bell13
measure bell13
cnot bell13 bell12
cnot bell12 x19
T* x19
H bell14
cnot bell14 bell15
cnot x8 bell15
measure bell15
cnot bell15 bell14
cnot bell14 x19
T x19
cnot bell12 x19
H bell12
measure bell12
cz bell12 x18
T* x19
cnot bell14 x19
H bell14
measure bell14
cz bell14 x8
H x19
H bell16
cnot bell16 bell17
cnot x8 bell17
measure bell17
cnot bell17 bell16
cnot bell16 x18
H 1
T 1
H bell18
cnot bell18 bell19
cnot x17 bell19
measure bell19
cnot bell19 bell18
cnot bell18 1
T* 1
H bell20
cnot bell20 bell21
cnot x7 bell21
measure bell21
cnot bell21 bell20
cnot bell20 1
T 1
cnot bell18 1
T* 1
cnot bell20 1
swap 2 6
H 1
T 0
cnot 1 0
T* 0
H bell22
cnot bell22 bell23
cnot x18 bell23
measure bell23
cnot bell23 bell22
cnot bell22 0
T 0
cnot 1 0
T* 0
cnot bell22 0
H 0
T x20
H bell24
cnot bell24 bell25
cnot 0 bell25
measure bell25
cnot bell25 bell24
cnot bell24 x20
T* x20
cnot x19 x20
T x20
cnot bell24 x20
H bell24
measure bell24
cz bell24 0
T* x20
cnot x19 x20
T 0
H bell26
cnot bell26 bell27
cnot x19 bell27
measure bell27
cnot bell27 bell26
cnot bell26 0
T* 0
cnot bell26 0
H bell26
measure bell26
cz bell26 x19
H 0
T* 0
cnot 1 0
T 0
cnot bell22 0
T* 0
cnot 1 0
T 0
cnot bell22 0
H bell22
measure bell22
cz bell22 x18
H 1
T* 1
cnot bell18 1
T 1
cnot bell20 1
T* 1
cnot bell18 1
T 1
cnot bell20 1
T 0
cnot bell18 0
T* 0
cnot bell20 0
T 0
cnot bell18 0
T* 0
cnot bell20 0
H 0
T x19
H x19
T x19
H bell28
cnot bell28 bell29
cnot 0 bell29
measure bell29
cnot bell29 bell28
cnot bell28 x19
T* x19
H bell30
cnot bell30 bell31
cnot x18 bell31
measure bell31
cnot bell31 bell30
cnot bell30 x19
T x19
cnot bell28 x19
H bell28
measure bell28
cz bell28 0
T* x19
cnot bell30 x19
H bell30
measure bell30
cz bell30 x18
H x19
T 0
H bell32
cnot bell32 bell33
cnot x18 bell33
measure bell33
cnot bell33 bell32
cnot bell32 0
T* 0
cnot bell32 0
H bell32
measure bell32
cz bell32 x18
swap 2 7
H 0
T* 0
cnot bell18 0
T 0
cnot bell20 0
T* 0
cnot bell18 0
H bell18
measure bell18
cz bell18 x17
T 0
cnot bell20 0
H bell20
measure bell20
cz bell20 x7
swap 2 6
cnot bell16 x18
T x18
cnot bell16 x18
H bell16
measure bell16
cz bell16 x8
H x18
T x18
H bell34
cnot bell34 bell35
cnot x17 bell35
measure bell35
cnot bell35 bell34
cnot bell34 x18
T* x18
H bell36
cnot bell36 bell37
cnot x7 bell37
measure bell37
cnot bell37 bell36
cnot bell36 x18
T x18
cnot bell34 x18
H bell34
measure bell34
cz bell34 x17
T* x18
cnot bell36 x18
H bell36
measure bell36
cz bell36 x7
H x18
H bell38
cnot bell38 bell39
cnot x7 bell39
measure bell39
cnot bell39 bell38
cnot bell38 x17
H 2
T 2
H bell40
cnot bell40 bell41
cnot x16 bell41
measure bell41
cnot bell41 bell40
cnot bell40 2
T* 2
H bell42
cnot bell42 bell43
cnot x6 bell43
measure bell43
cnot bell43 bell42
cnot bell42 2
T 2
cnot bell40 2
T* 2
cnot bell42 2
H 2
T 1
H bell44
cnot bell44 bell45
cnot 2 bell45
measure bell45
cnot bell45 bell44
cnot bell44 1
T* 1
H bell46
cnot bell46 bell47
cnot x17 bell47
measure bell47
cnot bell47 bell46
cnot bell46 1
T 1
cnot bell44 1
T* 1
cnot bell46 1
H 1
T 0
cnot 1 0
T* 0
H bell48
cnot bell48 bell49
cnot x18 bell49
measure bell49
cnot bell49 bell48
cnot bell48 0
T 0
cnot 1 0
T* 0
cnot bell48 0
H 0
T x20
H bell50
cnot bell50 bell51
cnot 0 bell51
measure bell51
cnot bell51 bell50
cnot bell50 x20
T* x20
cnot x19 x20
T x20
cnot bell50 x20
H bell50
measure bell50
cz bell50 0
T* x20
cnot x19 x20
T 0
H bell52
cnot bell52 bell53
cnot x19 bell53
measure bell53
cnot bell53 bell52
cnot bell52 0
T* 0
cnot bell52 0
H bell52
measure bell52
cz bell52 x19
H 0
T* 0
cnot 1 0
T 0
cnot bell48 0
T* 0
cnot 1 0
T 0
cnot bell48 0
H bell48
measure bell48
cz bell48 x18
H 1
T* 1
cnot bell44 1
T 1
cnot bell46 1
T* 1
cnot bell44 1
H bell44
measure bell44
cz bell44 2
T 1
cnot bell46 1
H 2
T* 2
cnot bell40 2
T 2
cnot bell42 2
T* 2
cnot bell40 2
H bell40
measure bell40
cz bell40 x16
T 2
cnot bell42 2
H bell42
measure bell42
cz bell42 x6
T 1
H bell54
cnot bell54 bell55
cnot x16 bell55
measure bell55
cnot bell55 bell54
cnot bell54 1
T* 1
H bell56
cnot bell56 bell57
cnot x6 bell57
measure bell57
cnot bell57 bell56
cnot bell56 1
T 1
cnot bell54 1
T* 1
cnot bell56 1
swap 3 5
H 1
T 0
cnot 1 0
T* 0
cnot bell46 0
T 0
cnot 1 0
T* 0
cnot bell46 0
H 0
T x19
H x19
T x19
H bell58
cnot bell58 bell59
cnot 0 bell59
measure bell59
cnot bell59 bell58
cnot bell58 x19
T* x19
H bell60
cnot bell60 bell61
cnot x18 bell61
measure bell61
cnot bell61 bell60
cnot bell60 x19
T x19
cnot bell58 x19
H bell58
measure bell58
cz bell58 0
T* x19
cnot bell60 x19
H bell60
measure bell60
cz bell60 x18
H x19
T 0
H bell62
cnot bell62 bell63
cnot x18 bell63
measure bell63
cnot bell63 bell62
cnot bell62 0
T* 0
cnot bell62 0
H bell62
measure bell62
cz bell62 x18
H 0
T* 0
cnot 1 0
T 0
cnot bell46 0
T* 0
cnot 1 0
T 0
cnot bell46 0
H bell46
measure bell46
cz bell46 x17
H 1
T* 1
cnot bell54 1
T 1
cnot bell56 1
T* 1
cnot bell54 1
T 1
cnot bell56 1
T 0
cnot bell54 0
T* 0
cnot bell56 0
T 0
cnot bell54 0
T* 0
cnot bell56 0
H 0
T x18
H x18
T x18
H bell64
cnot bell64 bell65
cnot 0 bell65
measure bell65
cnot bell65 bell64
cnot bell64 x18
T* x18
H bell66
cnot bell66 bell67
cnot x17 bell67
measure bell67
cnot bell67 bell66
cnot bell66 x18
T x18
cnot bell64 x18
H bell64
measure bell64
cz bell64 0
T* x18
cnot bell66 x18
H bell66
measure bell66
cz bell66 x17
H x18
T 0
H bell68
cnot bell68 bell69
cnot x17 bell69
measure bell69
cnot bell69 bell68
cnot bell68 0
T* 0
cnot bell68 0
H bell68
measure bell68
cz bell68 x17
swap 3 6
H 0
T* 0
cnot bell54 0
T 0
cnot bell56 0
T* 0
cnot bell54 0
H bell54
measure bell54
cz bell54 x16
T 0
cnot bell56 0
H bell56
measure bell56
cz bell56 x6
swap 3 5
cnot bell38 x17
T x17
cnot bell38 x17
H bell38
measure bell38
cz bell38 x7
H x17
T x17
H bell70
cnot bell70 bell71
cnot x16 bell71
measure bell71
cnot bell71 bell70
cnot bell70 x17
T* x17
H bell72
cnot bell72 bell73
cnot x6 bell73
measure bell73
cnot bell73 bell72
cnot bell72 x17
T x17
cnot bell70 x17
H bell70
measure bell70
cz bell70 x16
T* x17
cnot bell72 x17
H bell72
measure bell72
cz bell72 x6
H x17
H bell74
cnot bell74 bell75
cnot x6 bell75
measure bell75
cnot bell75 bell74
cnot bell74 x16
H 3
T 3
H bell76
cnot bell76 bell77
cnot x15 bell77
measure bell77
cnot bell77 bell76
cnot bell76 3
T* 3
H bell78
cnot bell78 bell79
cnot x5 bell79
measure bell79
cnot bell79 bell78
cnot bell78 3
T 3
cnot bell76 3
T* 3
cnot bell78 3
H 3
T 2
H bell80
cnot bell80 bell81
cnot 3 bell81
measure bell81
cnot bell81 bell80
cnot bell80 2
T* 2
H bell82
cnot bell82 bell83
cnot x16 bell83
measure bell83
cnot bell83 bell82
cnot bell82 2
T 2
cnot bell80 2
T* 2
cnot bell82 2
H 2
T 1
H bell84
cnot bell84 bell85
cnot 2 bell85
measure bell85
cnot bell85 bell84
cnot bell84 1
T* 1
H bell86
cnot bell86 bell87
cnot x17 bell87
measure bell87
cnot bell87 bell86
cnot bell86 1
T 1
cnot bell84 1
T* 1
cnot bell86 1
H 1
T 0
cnot 1 0
T* 0
H bell88
cnot bell88 bell89
cnot x18 bell89
measure bell89
cnot bell89 bell88
cnot bell88 0
T 0
cnot 1 0
T* 0
cnot bell88 0
H 0
T x20
H bell90
cnot bell90 bell91
cnot 0 bell91
measure bell91
cnot bell91 bell90
cnot bell90 x20
T* x20
cnot x19 x20
T x20
cnot bell90 x20
H bell90
measure bell90
cz bell90 0
T* x20
cnot x19 x20
T 0
H bell92
cnot bell92 bell93
cnot x19 bell93
measure bell93
cnot bell93 bell92
cnot bell92 0
T* 0
cnot bell92 0
H bell92
measure bell92
cz bell92 x19
H 0
T* 0
cnot 1 0
T 0
cnot bell88 0
T* 0
cnot 1 0
T 0
cnot bell88 0
H bell88
measure bell88
cz bell88 x18
H 1
T* 1
cnot bell84 1
T 1
cnot bell86 1
T* 1
cnot bell84 1
H bell84
measure bell84
cz bell84 2
T 1
cnot bell86 1
H 2
T* 2
cnot bell80 2
T 2
cnot bell82 2
T* 2
cnot bell80 2
H bell80
measure bell80
cz bell80 3
T 2
cnot bell82 2
H bell82
measure bell82
cz bell82 x16
H 3
T* 3
cnot bell76 3
T 3
cnot bell78 3
T* 3
cnot bell76 3
H bell76
measure bell76
cz bell76 x15
T 3
cnot bell78 3
H bell78
measure bell78
cz bell78 x5
T 2
H bell94
cnot bell94 bell95
cnot x15 bell95
measure bell95
cnot bell95 bell94
cnot bell94 2
T* 2
H bell96
cnot bell96 bell97
cnot x5 bell97
measure bell97
cnot bell97 bell96
cnot bell96 2
T 2
cnot bell94 2
T* 2
cnot bell96 2
H 2
T 1
H bell98
cnot bell98 bell99
cnot 2 bell99
measure bell99
cnot bell99 bell98
cnot bell98 1
T* 1
H bell100
cnot bell100 bell101
cnot x16 bell101
measure bell101
cnot bell101 bell100
cnot bell100 1
T 1
cnot bell98 1
T* 1
cnot bell100 1
H 1
T 0
cnot 1 0
T* 0
cnot bell86 0
T 0
cnot 1 0
T* 0
cnot bell86 0
H 0
T x19
H x19
T x19
H bell102
cnot bell102 bell103
cnot 0 bell103
measure bell103
cnot bell103 bell102
cnot bell102 x19
T* x19
H bell104
cnot bell104 bell105
cnot x18 bell105
measure bell105
cnot bell105 bell104
cnot bell104 x19
T x19
cnot bell102 x19
H bell102
measure bell102
cz bell102 0
T* x19
cnot bell104 x19
H bell104
measure bell104
cz bell104 x18
H x19
T 0
H bell106
cnot bell106 bell107
cnot x18 bell107
measure bell107
cnot bell107 bell106
cnot bell106 0
T* 0
cnot bell106 0
H bell106
measure bell106
cz bell106 x18
H 0
T* 0
cnot 1 0
T 0
cnot bell86 0
T* 0
cnot 1 0
T 0
cnot bell86 0
H bell86
measure bell86
cz bell86 x17
H 1
T* 1
cnot bell98 1
T 1
cnot bell100 1
T* 1
cnot bell98 1
H bell98
measure bell98
cz bell98 2
T 1
cnot bell100 1
H 2
T* 2
cnot bell94 2
T 2
cnot bell96 2
T* 2
cnot bell94 2
H bell94
measure bell94
cz bell94 x15
T 2
cnot bell96 2
H bell96
measure bell96
cz bell96 x5
T 1
H bell108
cnot bell108 bell109
cnot x15 bell109
measure bell109
cnot bell109 bell108
cnot bell108 1
T* 1
H bell110
cnot bell110 bell111
cnot x5 bell111
measure bell111
cnot bell111 bell110
cnot bell110 1
T 1
cnot bell108 1
T* 1
cnot bell110 1
H 1
T 0
cnot 1 0
T* 0
cnot bell100 0
T 0
cnot 1 0
T* 0
cnot bell100 0
H 0
T x18
H x18
T x18
H bell112
cnot bell112 bell113
cnot 0 bell113
measure bell113
cnot bell113 bell112
cnot bell112 x18
T* x18
H bell114
cnot bell114 bell115
cnot x17 bell115
measure bell115
cnot bell115 bell114
cnot bell114 x18
T x18
cnot bell112 x18
H bell112
measure bell112
cz bell112 0
T* x18
cnot bell114 x18
H bell114
measure bell114
cz bell114 x17
H x18
T 0
H bell116
cnot bell116 bell117
cnot x17 bell117
measure bell117
cnot bell117 bell116
cnot bell116 0
T* 0
cnot bell116 0
H bell116
measure bell116
cz bell116 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell100 0
T* 0
cnot 1 0
T 0
cnot bell100 0
H bell100
measure bell100
cz bell100 x16
H 1
T* 1
cnot bell108 1
T 1
cnot bell110 1
T* 1
cnot bell108 1
T 1
cnot bell110 1
T 0
cnot bell108 0
T* 0
cnot bell110 0
T 0
cnot bell108 0
T* 0
cnot bell110 0
H 0
T x17
H x17
T x17
H bell118
cnot bell118 bell119
cnot 0 bell119
measure bell119
cnot bell119 bell118
cnot bell118 x17
T* x17
H bell120
cnot bell120 bell121
cnot x16 bell121
measure bell121
cnot bell121 bell120
cnot bell120 x17
T x17
cnot bell118 x17
H bell118
measure bell118
cz bell118 0
T* x17
cnot bell120 x17
H bell120
measure bell120
cz bell120 x16
H x17
T 0
H bell122
cnot bell122 bell123
cnot x16 bell123
measure bell123
cnot bell123 bell122
cnot bell122 0
T* 0
cnot bell122 0
H bell122
measure bell122
cz bell122 x16
swap 4 5
H 0
T* 0
cnot bell108 0
T 0
cnot bell110 0
T* 0
cnot bell108 0
H bell108
measure bell108
cz bell108 x15
T 0
cnot bell110 0
H bell110
measure bell110
cz bell110 x5
cnot bell74 x16
T x16
cnot bell74 x16
H bell74
measure bell74
cz bell74 x6
H x16
T x16
cnot x15 x16
T* x16
H bell124
cnot bell124 bell125
cnot x5 bell125
measure bell125
cnot bell125 bell124
cnot bell124 x16
T x16
cnot x15 x16
T* x16
cnot bell124 x16
H x16
cnot bell124 x15
H 4
T 4
H bell126
cnot bell126 bell127
cnot x14 bell127
measure bell127
cnot bell127 bell126
cnot bell126 4
T* 4
H bell128
cnot bell128 bell129
cnot x4 bell129
measure bell129
cnot bell129 bell128
cnot bell128 4
T 4
cnot bell126 4
T* 4
cnot bell128 4
H 4
T 3
cnot 4 3
T* 3
H bell130
cnot bell130 bell131
cnot x15 bell131
measure bell131
cnot bell131 bell130
cnot bell130 3
T 3
cnot 4 3
T* 3
cnot bell130 3
H 3
T 2
H bell132
cnot bell132 bell133
cnot 3 bell133
measure bell133
cnot bell133 bell132
cnot bell132 2
T* 2
H bell134
cnot bell134 bell135
cnot x16 bell135
measure bell135
cnot bell135 bell134
cnot bell134 2
T 2
cnot bell132 2
T* 2
cnot bell134 2
H 2
T 1
H bell136
cnot bell136 bell137
cnot 2 bell137
measure bell137
cnot bell137 bell136
cnot bell136 1
T* 1
H bell138
cnot bell138 bell139
cnot x17 bell139
measure bell139
cnot bell139 bell138
cnot bell138 1
T 1
cnot bell136 1
T* 1
cnot bell138 1
H 1
T 0
cnot 1 0
T* 0
H bell140
cnot bell140 bell141
cnot x18 bell141
measure bell141
cnot bell141 bell140
cnot bell140 0
T 0
cnot 1 0
T* 0
cnot bell140 0
H 0
T x20
H bell142
cnot bell142 bell143
cnot 0 bell143
measure bell143
cnot bell143 bell142
cnot bell142 x20
T* x20
cnot x19 x20
T x20
cnot bell142 x20
H bell142
measure bell142
cz bell142 0
T* x20
cnot x19 x20
T 0
H bell144
cnot bell144 bell145
cnot x19 bell145
measure bell145
cnot bell145 bell144
cnot bell144 0
T* 0
cnot bell144 0
H bell144
measure bell144
cz bell144 x19
H 0
T* 0
cnot 1 0
T 0
cnot bell140 0
T* 0
cnot 1 0
T 0
cnot bell140 0
H bell140
measure bell140
cz bell140 x18
H 1
T* 1
cnot bell136 1
T 1
cnot bell138 1
T* 1
cnot bell136 1
H bell136
measure bell136
cz bell136 2
T 1
cnot bell138 1
H 2
T* 2
cnot bell132 2
T 2
cnot bell134 2
T* 2
cnot bell132 2
H bell132
measure bell132
cz bell132 3
T 2
cnot bell134 2
H bell134
measure bell134
cz bell134 x16
H 3
T* 3
cnot 4 3
T 3
cnot bell130 3
T* 3
cnot 4 3
T 3
cnot bell130 3
H bell130
measure bell130
cz bell130 x15
H 4
T* 4
cnot bell126 4
T 4
cnot bell128 4
T* 4
cnot bell126 4
T 4
cnot bell128 4
T 3
cnot bell126 3
T* 3
cnot bell128 3
T 3
cnot bell126 3
T* 3
cnot bell128 3
H 3
T 2
H bell146
cnot bell146 bell147
cnot 3 bell147
measure bell147
cnot bell147 bell146
cnot bell146 2
T* 2
H bell148
cnot bell148 bell149
cnot x15 bell149
measure bell149
cnot bell149 bell148
cnot bell148 2
T 2
cnot bell146 2
T* 2
cnot bell148 2
H 2
T 1
H bell150
cnot bell150 bell151
cnot 2 bell151
measure bell151
cnot bell151 bell150
cnot bell150 1
T* 1
H bell152
cnot bell152 bell153
cnot x16 bell153
measure bell153
cnot bell153 bell152
cnot bell152 1
T 1
cnot bell150 1
T* 1
cnot bell152 1
H 1
T 0
cnot 1 0
T* 0
cnot bell138 0
T 0
cnot 1 0
T* 0
cnot bell138 0
H 0
T x19
H x19
T x19
H bell154
cnot bell154 bell155
cnot 0 bell155
measure bell155
cnot bell155 bell154
cnot bell154 x19
T* x19
H bell156
cnot bell156 bell157
cnot x18 bell157
measure bell157
cnot bell157 bell156
cnot bell156 x19
T x19
cnot bell154 x19
H bell154
measure bell154
cz bell154 0
T* x19
cnot bell156 x19
H bell156
measure bell156
cz bell156 x18
H x19
T 0
H bell158
cnot bell158 bell159
cnot x18 bell159
measure bell159
cnot bell159 bell158
cnot bell158 0
T* 0
cnot bell158 0
H bell158
measure bell158
cz bell158 x18
H 0
T* 0
cnot 1 0
T 0
cnot bell138 0
T* 0
cnot 1 0
T 0
cnot bell138 0
H bell138
measure bell138
cz bell138 x17
H 1
T* 1
cnot bell150 1
T 1
cnot bell152 1
T* 1
cnot bell150 1
H bell150
measure bell150
cz bell150 2
T 1
cnot bell152 1
H 2
T* 2
cnot bell146 2
T 2
cnot bell148 2
T* 2
cnot bell146 2
H bell146
measure bell146
cz bell146 3
T 2
cnot bell148 2
H bell148
measure bell148
cz bell148 x15
H 3
T* 3
cnot bell126 3
T 3
cnot bell128 3
T* 3
cnot bell126 3
H bell126
measure bell126
cz bell126 x14
T 3
cnot bell128 3
H bell128
measure bell128
cz bell128 x4
T 2
H bell160
cnot bell160 bell161
cnot x14 bell161
measure bell161
cnot bell161 bell160
cnot bell160 2
T* 2
H bell162
cnot bell162 bell163
cnot x4 bell163
measure bell163
cnot bell163 bell162
cnot bell162 2
T 2
cnot bell160 2
T* 2
cnot bell162 2
H 2
T 1
H bell164
cnot bell164 bell165
cnot 2 bell165
measure bell165
cnot bell165 bell164
cnot bell164 1
T* 1
H bell166
cnot bell166 bell167
cnot x15 bell167
measure bell167
cnot bell167 bell166
cnot bell166 1
T 1
cnot bell164 1
T* 1
cnot bell166 1
H 1
T 0
cnot 1 0
T* 0
cnot bell152 0
T 0
cnot 1 0
T* 0
cnot bell152 0
H 0
T x18
H x18
T x18
H bell168
cnot bell168 bell169
cnot 0 bell169
measure bell169
cnot bell169 bell168
cnot bell168 x18
T* x18
H bell170
cnot bell170 bell171
cnot x17 bell171
measure bell171
cnot bell171 bell170
cnot bell170 x18
T x18
cnot bell168 x18
H bell168
measure bell168
cz bell168 0
T* x18
cnot bell170 x18
H bell170
measure bell170
cz bell170 x17
H x18
T 0
H bell172
cnot bell172 bell173
cnot x17 bell173
measure bell173
cnot bell173 bell172
cnot bell172 0
T* 0
cnot bell172 0
H bell172
measure bell172
cz bell172 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell152 0
T* 0
cnot 1 0
T 0
cnot bell152 0
H bell152
measure bell152
cz bell152 x16
H 1
T* 1
cnot bell164 1
T 1
cnot bell166 1
T* 1
cnot bell164 1
H bell164
measure bell164
cz bell164 2
T 1
cnot bell166 1
H 2
T* 2
cnot bell160 2
T 2
cnot bell162 2
T* 2
cnot bell160 2
H bell160
measure bell160
cz bell160 x14
T 2
cnot bell162 2
H bell162
measure bell162
cz bell162 x4
T 1
H bell174
cnot bell174 bell175
cnot x14 bell175
measure bell175
cnot bell175 bell174
cnot bell174 1
T* 1
H bell176
cnot bell176 bell177
cnot x4 bell177
measure bell177
cnot bell177 bell176
cnot bell176 1
T 1
cnot bell174 1
T* 1
cnot bell176 1
H 1
T 0
cnot 1 0
T* 0
cnot bell166 0
T 0
cnot 1 0
T* 0
cnot bell166 0
H 0
T x17
H x17
T x17
H bell178
cnot bell178 bell179
cnot 0 bell179
measure bell179
cnot bell179 bell178
cnot bell178 x17
T* x17
H bell180
cnot bell180 bell181
cnot x16 bell181
measure bell181
cnot bell181 bell180
cnot bell180 x17
T x17
cnot bell178 x17
H bell178
measure bell178
cz bell178 0
T* x17
cnot bell180 x17
H bell180
measure bell180
cz bell180 x16
H x17
T 0
H bell182
cnot bell182 bell183
cnot x16 bell183
measure bell183
cnot bell183 bell182
cnot bell182 0
T* 0
cnot bell182 0
H bell182
measure bell182
cz bell182 x16
H 0
T* 0
cnot 1 0
T 0
cnot bell166 0
T* 0
cnot 1 0
T 0
cnot bell166 0
H 1
T* 1
cnot bell174 1
T 1
cnot bell176 1
T* 1
cnot bell174 1
T 1
cnot bell176 1
T 0
cnot bell174 0
T* 0
cnot bell176 0
T 0
cnot bell174 0
T* 0
cnot bell176 0
H 0
T x16
H x16
T x16
H bell184
cnot bell184 bell185
cnot 0 bell185
measure bell185
cnot bell185 bell184
cnot bell184 x16
T* x16
cnot x15 x16
T x16
cnot bell184 x16
H bell184
measure bell184
cz bell184 0
T* x16
cnot x15 x16
H x16
T 0
cnot bell166 0
T* 0
cnot bell166 0
H bell166
measure bell166
cz bell166 x15
H 0
T* 0
cnot bell174 0
T 0
cnot bell176 0
T* 0
cnot bell174 0
H bell174
measure bell174
cz bell174 x14
T 0
cnot bell176 0
H bell176
measure bell176
cz bell176 x4
cnot bell124 x15
T x15
cnot bell124 x15
H bell124
measure bell124
cz bell124 x5
H x15
T x15
H bell186
cnot bell186 bell187
cnot x14 bell187
measure bell187
cnot bell187 bell186
cnot bell186 x15
T* x15
H bell188
cnot bell188 bell189
cnot x4 bell189
measure bell189
cnot bell189 bell188
cnot bell188 x15
T x15
cnot bell186 x15
H bell186
measure bell186
cz bell186 x14
T* x15
cnot bell188 x15
H bell188
measure bell188
cz bell188 x4
H x15
H bell190
cnot bell190 bell191
cnot x4 bell191
measure bell191
cnot bell191 bell190
cnot bell190 x14
H 5
T 5
H bell192
cnot bell192 bell193
cnot x13 bell193
measure bell193
cnot bell193 bell192
cnot bell192 5
T* 5
H bell194
cnot bell194 bell195
cnot x3 bell195
measure bell195
cnot bell195 bell194
cnot bell194 5
T 5
cnot bell192 5
T* 5
cnot bell194 5
H 5
T 4
H bell196
cnot bell196 bell197
cnot 5 bell197
measure bell197
cnot bell197 bell196
cnot bell196 4
T* 4
H bell198
cnot bell198 bell199
cnot x14 bell199
measure bell199
cnot bell199 bell198
cnot bell198 4
T 4
cnot bell196 4
T* 4
cnot bell198 4
H 4
T 3
cnot 4 3
T* 3
H bell200
cnot bell200 bell201
cnot x15 bell201
measure bell201
cnot bell201 bell200
cnot bell200 3
T 3
cnot 4 3
T* 3
cnot bell200 3
H 3
T 2
H bell202
cnot bell202 bell203
cnot 3 bell203
measure bell203
cnot bell203 bell202
cnot bell202 2
T* 2
H bell204
cnot bell204 bell205
cnot x16 bell205
measure bell205
cnot bell205 bell204
cnot bell204 2
T 2
cnot bell202 2
T* 2
cnot bell204 2
H 2
T 1
H bell206
cnot bell206 bell207
cnot 2 bell207
measure bell207
cnot bell207 bell206
cnot bell206 1
T* 1
H bell208
cnot bell208 bell209
cnot x17 bell209
measure bell209
cnot bell209 bell208
cnot bell208 1
T 1
cnot bell206 1
T* 1
cnot bell208 1
H 1
T 0
cnot 1 0
T* 0
H bell210
cnot bell210 bell211
cnot x18 bell211
measure bell211
cnot bell211 bell210
cnot bell210 0
T 0
cnot 1 0
T* 0
cnot bell210 0
H 0
T x20
H bell212
cnot bell212 bell213
cnot 0 bell213
measure bell213
cnot bell213 bell212
cnot bell212 x20
T* x20
cnot x19 x20
T x20
cnot bell212 x20
H bell212
measure bell212
cz bell212 0
T* x20
cnot x19 x20
T 0
H bell214
cnot bell214 bell215
cnot x19 bell215
measure bell215
cnot bell215 bell214
cnot bell214 0
T* 0
cnot bell214 0
H bell214
measure bell214
cz bell214 x19
H 0
T* 0
cnot 1 0
T 0
cnot bell210 0
T* 0
cnot 1 0
T 0
cnot bell210 0
H bell210
measure bell210
cz bell210 x18
H 1
T* 1
cnot bell206 1
T 1
cnot bell208 1
T* 1
cnot bell206 1
H bell206
measure bell206
cz bell206 2
T 1
cnot bell208 1
H 2
T* 2
cnot bell202 2
T 2
cnot bell204 2
T* 2
cnot bell202 2
H bell202
measure bell202
cz bell202 3
T 2
cnot bell204 2
H bell204
measure bell204
cz bell204 x16
H 3
T* 3
cnot 4 3
T 3
cnot bell200 3
T* 3
cnot 4 3
T 3
cnot bell200 3
H bell200
measure bell200
cz bell200 x15
H 4
T* 4
cnot bell196 4
T 4
cnot bell198 4
T* 4
cnot bell196 4
H bell196
measure bell196
cz bell196 5
T 4
cnot bell198 4
H 5
T* 5
cnot bell192 5
T 5
cnot bell194 5
T* 5
cnot bell192 5
H bell192
measure bell192
cz bell192 x13
T 5
cnot bell194 5
H bell194
measure bell194
cz bell194 x3
T 4
H bell216
cnot bell216 bell217
cnot x13 bell217
measure bell217
cnot bell217 bell216
cnot bell216 4
T* 4
H bell218
cnot bell218 bell219
cnot x3 bell219
measure bell219
cnot bell219 bell218
cnot bell218 4
T 4
cnot bell216 4
T* 4
cnot bell218 4
H 4
T 3
cnot 4 3
T* 3
cnot bell198 3
T 3
cnot 4 3
T* 3
cnot bell198 3
H 3
T 2
H bell220
cnot bell220 bell221
cnot 3 bell221
measure bell221
cnot bell221 bell220
cnot bell220 2
T* 2
H bell222
cnot bell222 bell223
cnot x15 bell223
measure bell223
cnot bell223 bell222
cnot bell222 2
T 2
cnot bell220 2
T* 2
cnot bell222 2
H 2
T 1
H bell224
cnot bell224 bell225
cnot 2 bell225
measure bell225
cnot bell225 bell224
cnot bell224 1
T* 1
H bell226
cnot bell226 bell227
cnot x16 bell227
measure bell227
cnot bell227 bell226
cnot bell226 1
T 1
cnot bell224 1
T* 1
cnot bell226 1
H 1
T 0
cnot 1 0
T* 0
cnot bell208 0
T 0
cnot 1 0
T* 0
cnot bell208 0
H 0
T x19
H x19
T x19
H bell228
cnot bell228 bell229
cnot 0 bell229
measure bell229
cnot bell229 bell228
cnot bell228 x19
T* x19
H bell230
cnot bell230 bell231
cnot x18 bell231
measure bell231
cnot bell231 bell230
cnot bell230 x19
T x19
cnot bell228 x19
H bell228
measure bell228
cz bell228 0
T* x19
cnot bell230 x19
H bell230
measure bell230
cz bell230 x18
H x19
T 0
H bell232
cnot bell232 bell233
cnot x18 bell233
measure bell233
cnot bell233 bell232
cnot bell232 0
T* 0
cnot bell232 0
H bell232
measure bell232
cz bell232 x18
H 0
T* 0
cnot 1 0
T 0
cnot bell208 0
T* 0
cnot 1 0
T 0
cnot bell208 0
H bell208
measure bell208
cz bell208 x17
H 1
T* 1
cnot bell224 1
T 1
cnot bell226 1
T* 1
cnot bell224 1
H bell224
measure bell224
cz bell224 2
T 1
cnot bell226 1
H 2
T* 2
cnot bell220 2
T 2
cnot bell222 2
T* 2
cnot bell220 2
H bell220
measure bell220
cz bell220 3
T 2
cnot bell222 2
H bell222
measure bell222
cz bell222 x15
H 3
T* 3
cnot 4 3
T 3
cnot bell198 3
T* 3
cnot 4 3
T 3
cnot bell198 3
H bell198
measure bell198
cz bell198 x14
H 4
T* 4
cnot bell216 4
T 4
cnot bell218 4
T* 4
cnot bell216 4
T 4
cnot bell218 4
T 3
cnot bell216 3
T* 3
cnot bell218 3
T 3
cnot bell216 3
T* 3
cnot bell218 3
H 3
T 2
H bell234
cnot bell234 bell235
cnot 3 bell235
measure bell235
cnot bell235 bell234
cnot bell234 2
T* 2
H bell236
cnot bell236 bell237
cnot x14 bell237
measure bell237
cnot bell237 bell236
cnot bell236 2
T 2
cnot bell234 2
T* 2
cnot bell236 2
H 2
T 1
H bell238
cnot bell238 bell239
cnot 2 bell239
measure bell239
cnot bell239 bell238
cnot bell238 1
T* 1
H bell240
cnot bell240 bell241
cnot x15 bell241
measure bell241
cnot bell241 bell240
cnot bell240 1
T 1
cnot bell238 1
T* 1
cnot bell240 1
H 1
T 0
cnot 1 0
T* 0
cnot bell226 0
T 0
cnot 1 0
T* 0
cnot bell226 0
H 0
T x18
H x18
T x18
H bell242
cnot bell242 bell243
cnot 0 bell243
measure bell243
cnot bell243 bell242
cnot bell242 x18
T* x18
H bell244
cnot bell244 bell245
cnot x17 bell245
measure bell245
cnot bell245 bell244
cnot bell244 x18
T x18
cnot bell242 x18
H bell242
measure bell242
cz bell242 0
T* x18
cnot bell244 x18
H bell244
measure bell244
cz bell244 x17
H x18
T 0
H bell246
cnot bell246 bell247
cnot x17 bell247
measure bell247
cnot bell247 bell246
cnot bell246 0
T* 0
cnot bell246 0
H bell246
measure bell246
cz bell246 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell226 0
T* 0
cnot 1 0
T 0
cnot bell226 0
H bell226
measure bell226
cz bell226 x16
H 1
T* 1
cnot bell238 1
T 1
cnot bell240 1
T* 1
cnot bell238 1
H bell238
measure bell238
cz bell238 2
T 1
cnot bell240 1
H 2
T* 2
cnot bell234 2
T 2
cnot bell236 2
T* 2
cnot bell234 2
H bell234
measure bell234
cz bell234 3
T 2
cnot bell236 2
H bell236
measure bell236
cz bell236 x14
H 3
T* 3
cnot bell216 3
T 3
cnot bell218 3
T* 3
cnot bell216 3
H bell216
measure bell216
cz bell216 x13
T 3
cnot bell218 3
H bell218
measure bell218
cz bell218 x3
T 2
H bell248
cnot bell248 bell249
cnot x13 bell249
measure bell249
cnot bell249 bell248
cnot bell248 2
T* 2
H bell250
cnot bell250 bell251
cnot x3 bell251
measure bell251
cnot bell251 bell250
cnot bell250 2
T 2
cnot bell248 2
T* 2
cnot bell250 2
H 2
T 1
H bell252
cnot bell252 bell253
cnot 2 bell253
measure bell253
cnot bell253 bell252
cnot bell252 1
T* 1
H bell254
cnot bell254 bell255
cnot x14 bell255
measure bell255
cnot bell255 bell254
cnot bell254 1
T 1
cnot bell252 1
T* 1
cnot bell254 1
H 1
T 0
cnot 1 0
T* 0
cnot bell240 0
T 0
cnot 1 0
T* 0
cnot bell240 0
H 0
T x17
H x17
T x17
H bell256
cnot bell256 bell257
cnot 0 bell257
measure bell257
cnot bell257 bell256
cnot bell256 x17
T* x17
H bell258
cnot bell258 bell259
cnot x16 bell259
measure bell259
cnot bell259 bell258
cnot bell258 x17
T x17
cnot bell256 x17
H bell256
measure bell256
cz bell256 0
T* x17
cnot bell258 x17
H bell258
measure bell258
cz bell258 x16
H x17
T 0
H bell260
cnot bell260 bell261
cnot x16 bell261
measure bell261
cnot bell261 bell260
cnot bell260 0
T* 0
cnot bell260 0
H bell260
measure bell260
cz bell260 x16
H 0
T* 0
cnot 1 0
T 0
cnot bell240 0
T* 0
cnot 1 0
T 0
cnot bell240 0
H 1
T* 1
cnot bell252 1
T 1
cnot bell254 1
T* 1
cnot bell252 1
H bell252
measure bell252
cz bell252 2
T 1
cnot bell254 1
H 2
T* 2
cnot bell248 2
T 2
cnot bell250 2
T* 2
cnot bell248 2
H bell248
measure bell248
cz bell248 x13
T 2
cnot bell250 2
H bell250
measure bell250
cz bell250 x3
T 1
H bell262
cnot bell262 bell263
cnot x13 bell263
measure bell263
cnot bell263 bell262
cnot bell262 1
T* 1
H bell264
cnot bell264 bell265
cnot x3 bell265
measure bell265
cnot bell265 bell264
cnot bell264 1
T 1
cnot bell262 1
T* 1
cnot bell264 1
H 1
T 0
cnot 1 0
T* 0
cnot bell254 0
T 0
cnot 1 0
T* 0
cnot bell254 0
H 0
T x16
H x16
T x16
H bell266
cnot bell266 bell267
cnot 0 bell267
measure bell267
cnot bell267 bell266
cnot bell266 x16
T* x16
cnot x15 x16
T x16
cnot bell266 x16
H bell266
measure bell266
cz bell266 0
T* x16
cnot x15 x16
H x16
T 0
cnot bell240 0
T* 0
cnot bell240 0
H bell240
measure bell240
cz bell240 x15
H 0
T* 0
cnot 1 0
T 0
cnot bell254 0
T* 0
cnot 1 0
T 0
cnot bell254 0
H bell254
measure bell254
cz bell254 x14
H 1
T* 1
cnot bell262 1
T 1
cnot bell264 1
T* 1
cnot bell262 1
T 1
cnot bell264 1
T 0
cnot bell262 0
T* 0
cnot bell264 0
T 0
cnot bell262 0
T* 0
cnot bell264 0
H 0
T x15
H x15
T x15
H bell268
cnot bell268 bell269
cnot 0 bell269
measure bell269
cnot bell269 bell268
cnot bell268 x15
T* x15
H bell270
cnot bell270 bell271
cnot x14 bell271
measure bell271
cnot bell271 bell270
cnot bell270 x15
T x15
cnot bell268 x15
H bell268
measure bell268
cz bell268 0
T* x15
cnot bell270 x15
H bell270
measure bell270
cz bell270 x14
H x15
T 0
H bell272
cnot bell272 bell273
cnot x14 bell273
measure bell273
cnot bell273 bell272
cnot bell272 0
T* 0
cnot bell272 0
H bell272
measure bell272
cz bell272 x14
H 0
T* 0
cnot bell262 0
T 0
cnot bell264 0
T* 0
cnot bell262 0
H bell262
measure bell262
cz bell262 x13
T 0
cnot bell264 0
H bell264
measure bell264
cz bell264 x3
cnot bell190 x14
T x14
cnot bell190 x14
H bell190
measure bell190
cz bell190 x4
H x14
T x14
cnot x13 x14
T* x14
H bell274
cnot bell274 bell275
cnot x3 bell275
measure bell275
cnot bell275 bell274
cnot bell274 x14
T x14
cnot x13 x14
T* x14
cnot bell274 x14
H x14
cnot bell274 x13
H 6
T 6
H bell276
cnot bell276 bell277
cnot x12 bell277
measure bell277
cnot bell277 bell276
cnot bell276 6
T* 6
H bell278
cnot bell278 bell279
cnot x2 bell279
measure bell279
cnot bell279 bell278
cnot bell278 6
T 6
cnot bell276 6
T* 6
cnot bell278 6
H 6
T 5
cnot 6 5
T* 5
H bell280
cnot bell280 bell281
cnot x13 bell281
measure bell281
cnot bell281 bell280
cnot bell280 5
T 5
cnot 6 5
T* 5
cnot bell280 5
H 5
T 4
H bell282
cnot bell282 bell283
cnot 5 bell283
measure bell283
cnot bell283 bell282
cnot bell282 4
T* 4
H bell284
cnot bell284 bell285
cnot x14 bell285
measure bell285
cnot bell285 bell284
cnot bell284 4
T 4
cnot bell282 4
T* 4
cnot bell284 4
H 4
T 3
cnot 4 3
T* 3
H bell286
cnot bell286 bell287
cnot x15 bell287
measure bell287
cnot bell287 bell286
cnot bell286 3
T 3
cnot 4 3
T* 3
cnot bell286 3
H 3
T 2
H bell288
cnot bell288 bell289
cnot 3 bell289
measure bell289
cnot bell289 bell288
cnot bell288 2
T* 2
H bell290
cnot bell290 bell291
cnot x16 bell291
measure bell291
cnot bell291 bell290
cnot bell290 2
T 2
cnot bell288 2
T* 2
cnot bell290 2
H 2
T 1
H bell292
cnot bell292 bell293
cnot 2 bell293
measure bell293
cnot bell293 bell292
cnot bell292 1
T* 1
H bell294
cnot bell294 bell295
cnot x17 bell295
measure bell295
cnot bell295 bell294
cnot bell294 1
T 1
cnot bell292 1
T* 1
cnot bell294 1
H 1
T 0
cnot 1 0
T* 0
H bell296
cnot bell296 bell297
cnot x18 bell297
measure bell297
cnot bell297 bell296
cnot bell296 0
T 0
cnot 1 0
T* 0
cnot bell296 0
H 0
T x20
H bell298
cnot bell298 bell299
cnot 0 bell299
measure bell299
cnot bell299 bell298
cnot bell298 x20
T* x20
cnot x19 x20
T x20
cnot bell298 x20
H bell298
measure bell298
cz bell298 0
T* x20
cnot x19 x20
T 0
H bell300
cnot bell300 bell301
cnot x19 bell301
measure bell301
cnot bell301 bell300
cnot bell300 0
T* 0
cnot bell300 0
H bell300
measure bell300
cz bell300 x19
H 0
T* 0
cnot 1 0
T 0
cnot bell296 0
T* 0
cnot 1 0
T 0
cnot bell296 0
H bell296
measure bell296
cz bell296 x18
H 1
T* 1
cnot bell292 1
T 1
cnot bell294 1
T* 1
cnot bell292 1
H bell292
measure bell292
cz bell292 2
T 1
cnot bell294 1
H 2
T* 2
cnot bell288 2
T 2
cnot bell290 2
T* 2
cnot bell288 2
H bell288
measure bell288
cz bell288 3
T 2
cnot bell290 2
H bell290
measure bell290
cz bell290 x16
H 3
T* 3
cnot 4 3
T 3
cnot bell286 3
T* 3
cnot 4 3
T 3
cnot bell286 3
H bell286
measure bell286
cz bell286 x15
H 4
T* 4
cnot bell282 4
T 4
cnot bell284 4
T* 4
cnot bell282 4
H bell282
measure bell282
cz bell282 5
T 4
cnot bell284 4
H 5
T* 5
cnot 6 5
T 5
cnot bell280 5
T* 5
cnot 6 5
T 5
cnot bell280 5
H bell280
measure bell280
cz bell280 x13
H 6
T* 6
cnot bell276 6
T 6
cnot bell278 6
T* 6
cnot bell276 6
T 6
cnot bell278 6
T 5
cnot bell276 5
T* 5
cnot bell278 5
T 5
cnot bell276 5
T* 5
cnot bell278 5
H 5
T 4
H bell302
cnot bell302 bell303
cnot 5 bell303
measure bell303
cnot bell303 bell302
cnot bell302 4
T* 4
H bell304
cnot bell304 bell305
cnot x13 bell305
measure bell305
cnot bell305 bell304
cnot bell304 4
T 4
cnot bell302 4
T* 4
cnot bell304 4
H 4
T 3
cnot 4 3
T* 3
cnot bell284 3
T 3
cnot 4 3
T* 3
cnot bell284 3
H 3
T 2
H bell306
cnot bell306 bell307
cnot 3 bell307
measure bell307
cnot bell307 bell306
cnot bell306 2
T* 2
H bell308
cnot bell308 bell309
cnot x15 bell309
measure bell309
cnot bell309 bell308
cnot bell308 2
T 2
cnot bell306 2
T* 2
cnot bell308 2
H 2
T 1
H bell310
cnot bell310 bell311
cnot 2 bell311
measure bell311
cnot bell311 bell310
cnot bell310 1
T* 1
H bell312
cnot bell312 bell313
cnot x16 bell313
measure bell313
cnot bell313 bell312
cnot bell312 1
T 1
cnot bell310 1
T* 1
cnot bell312 1
H 1
T 0
cnot 1 0
T* 0
cnot bell294 0
T 0
cnot 1 0
T* 0
cnot bell294 0
H 0
T x19
H x19
T x19
H bell314
cnot bell314 bell315
cnot 0 bell315
measure bell315
cnot bell315 bell314
cnot bell314 x19
T* x19
H bell316
cnot bell316 bell317
cnot x18 bell317
measure bell317
cnot bell317 bell316
cnot bell316 x19
T x19
cnot bell314 x19
H bell314
measure bell314
cz bell314 0
T* x19
cnot bell316 x19
H bell316
measure bell316
cz bell316 x18
H x19
T 0
H bell318
cnot bell318 bell319
cnot x18 bell319
measure bell319
cnot bell319 bell318
cnot bell318 0
T* 0
cnot bell318 0
H bell318
measure bell318
cz bell318 x18
H 0
T* 0
cnot 1 0
T 0
cnot bell294 0
T* 0
cnot 1 0
T 0
cnot bell294 0
H bell294
measure bell294
cz bell294 x17
H 1
T* 1
cnot bell310 1
T 1
cnot bell312 1
T* 1
cnot bell310 1
H bell310
measure bell310
cz bell310 2
T 1
cnot bell312 1
H 2
T* 2
cnot bell306 2
T 2
cnot bell308 2
T* 2
cnot bell306 2
H bell306
measure bell306
cz bell306 3
T 2
cnot bell308 2
H bell308
measure bell308
cz bell308 x15
H 3
T* 3
cnot 4 3
T 3
cnot bell284 3
T* 3
cnot 4 3
T 3
cnot bell284 3
H bell284
measure bell284
cz bell284 x14
H 4
T* 4
cnot bell302 4
T 4
cnot bell304 4
T* 4
cnot bell302 4
H bell302
measure bell302
cz bell302 5
T 4
cnot bell304 4
H 5
T* 5
cnot bell276 5
T 5
cnot bell278 5
T* 5
cnot bell276 5
H bell276
measure bell276
cz bell276 x12
T 5
cnot bell278 5
H bell278
measure bell278
cz bell278 x2
T 4
H bell320
cnot bell320 bell321
cnot x12 bell321
measure bell321
cnot bell321 bell320
cnot bell320 4
T* 4
H bell322
cnot bell322 bell323
cnot x2 bell323
measure bell323
cnot bell323 bell322
cnot bell322 4
T 4
cnot bell320 4
T* 4
cnot bell322 4
H 4
T 3
cnot 4 3
T* 3
cnot bell304 3
T 3
cnot 4 3
T* 3
cnot bell304 3
H 3
T 2
H bell324
cnot bell324 bell325
cnot 3 bell325
measure bell325
cnot bell325 bell324
cnot bell324 2
T* 2
H bell326
cnot bell326 bell327
cnot x14 bell327
measure bell327
cnot bell327 bell326
cnot bell326 2
T 2
cnot bell324 2
T* 2
cnot bell326 2
H 2
T 1
H bell328
cnot bell328 bell329
cnot 2 bell329
measure bell329
cnot bell329 bell328
cnot bell328 1
T* 1
H bell330
cnot bell330 bell331
cnot x15 bell331
measure bell331
cnot bell331 bell330
cnot bell330 1
T 1
cnot bell328 1
T* 1
cnot bell330 1
H 1
T 0
cnot 1 0
T* 0
cnot bell312 0
T 0
cnot 1 0
T* 0
cnot bell312 0
H 0
T x18
H x18
T x18
H bell332
cnot bell332 bell333
cnot 0 bell333
measure bell333
cnot bell333 bell332
cnot bell332 x18
T* x18
H bell334
cnot bell334 bell335
cnot x17 bell335
measure bell335
cnot bell335 bell334
cnot bell334 x18
T x18
cnot bell332 x18
H bell332
measure bell332
cz bell332 0
T* x18
cnot bell334 x18
H bell334
measure bell334
cz bell334 x17
H x18
T 0
H bell336
cnot bell336 bell337
cnot x17 bell337
measure bell337
cnot bell337 bell336
cnot bell336 0
T* 0
cnot bell336 0
H bell336
measure bell336
cz bell336 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell312 0
T* 0
cnot 1 0
T 0
cnot bell312 0
H bell312
measure bell312
cz bell312 x16
H 1
T* 1
cnot bell328 1
T 1
cnot bell330 1
T* 1
cnot bell328 1
H bell328
measure bell328
cz bell328 2
T 1
cnot bell330 1
H 2
T* 2
cnot bell324 2
T 2
cnot bell326 2
T* 2
cnot bell324 2
H bell324
measure bell324
cz bell324 3
T 2
cnot bell326 2
H bell326
measure bell326
cz bell326 x14
H 3
T* 3
cnot 4 3
T 3
cnot bell304 3
T* 3
cnot 4 3
T 3
cnot bell304 3
H bell304
measure bell304
cz bell304 x13
H 4
T* 4
cnot bell320 4
T 4
cnot bell322 4
T* 4
cnot bell320 4
T 4
cnot bell322 4
T 3
cnot bell320 3
T* 3
cnot bell322 3
T 3
cnot bell320 3
T* 3
cnot bell322 3
H 3
T 2
H bell338
cnot bell338 bell339
cnot 3 bell339
measure bell339
cnot bell339 bell338
cnot bell338 2
T* 2
H bell340
cnot bell340 bell341
cnot x13 bell341
measure bell341
cnot bell341 bell340
cnot bell340 2
T 2
cnot bell338 2
T* 2
cnot bell340 2
H 2
T 1
H bell342
cnot bell342 bell343
cnot 2 bell343
measure bell343
cnot bell343 bell342
cnot bell342 1
T* 1
H bell344
cnot bell344 bell345
cnot x14 bell345
measure bell345
cnot bell345 bell344
cnot bell344 1
T 1
cnot bell342 1
T* 1
cnot bell344 1
H 1
T 0
cnot 1 0
T* 0
cnot bell330 0
T 0
cnot 1 0
T* 0
cnot bell330 0
H 0
T x17
H x17
T x17
H bell346
cnot bell346 bell347
cnot 0 bell347
measure bell347
cnot bell347 bell346
cnot bell346 x17
T* x17
H bell348
cnot bell348 bell349
cnot x16 bell349
measure bell349
cnot bell349 bell348
cnot bell348 x17
T x17
cnot bell346 x17
H bell346
measure bell346
cz bell346 0
T* x17
cnot bell348 x17
H bell348
measure bell348
cz bell348 x16
H x17
T 0
H bell350
cnot bell350 bell351
cnot x16 bell351
measure bell351
cnot bell351 bell350
cnot bell350 0
T* 0
cnot bell350 0
H bell350
measure bell350
cz bell350 x16
H 0
T* 0
cnot 1 0
T 0
cnot bell330 0
T* 0
cnot 1 0
T 0
cnot bell330 0
H 1
T* 1
cnot bell342 1
T 1
cnot bell344 1
T* 1
cnot bell342 1
H bell342
measure bell342
cz bell342 2
T 1
cnot bell344 1
H 2
T* 2
cnot bell338 2
T 2
cnot bell340 2
T* 2
cnot bell338 2
H bell338
measure bell338
cz bell338 3
T 2
cnot bell340 2
H bell340
measure bell340
cz bell340 x13
H 3
T* 3
cnot bell320 3
T 3
cnot bell322 3
T* 3
cnot bell320 3
H bell320
measure bell320
cz bell320 x12
T 3
cnot bell322 3
H bell322
measure bell322
cz bell322 x2
T 2
H bell352
cnot bell352 bell353
cnot x12 bell353
measure bell353
cnot bell353 bell352
cnot bell352 2
T* 2
H bell354
cnot bell354 bell355
cnot x2 bell355
measure bell355
cnot bell355 bell354
cnot bell354 2
T 2
cnot bell352 2
T* 2
cnot bell354 2
H 2
T 1
H bell356
cnot bell356 bell357
cnot 2 bell357
measure bell357
cnot bell357 bell356
cnot bell356 1
T* 1
H bell358
cnot bell358 bell359
cnot x13 bell359
measure bell359
cnot bell359 bell358
cnot bell358 1
T 1
cnot bell356 1
T* 1
cnot bell358 1
H 1
T 0
cnot 1 0
T* 0
cnot bell344 0
T 0
cnot 1 0
T* 0
cnot bell344 0
H 0
T x16
H x16
T x16
H bell360
cnot bell360 bell361
cnot 0 bell361
measure bell361
cnot bell361 bell360
cnot bell360 x16
T* x16
cnot x15 x16
T x16
cnot bell360 x16
H bell360
measure bell360
cz bell360 0
T* x16
cnot x15 x16
H x16
T 0
cnot bell330 0
T* 0
cnot bell330 0
H bell330
measure bell330
cz bell330 x15
H 0
T* 0
cnot 1 0
T 0
cnot bell344 0
T* 0
cnot 1 0
T 0
cnot bell344 0
H bell344
measure bell344
cz bell344 x14
H 1
T* 1
cnot bell356 1
T 1
cnot bell358 1
T* 1
cnot bell356 1
H bell356
measure bell356
cz bell356 2
T 1
cnot bell358 1
H 2
T* 2
cnot bell352 2
T 2
cnot bell354 2
T* 2
cnot bell352 2
H bell352
measure bell352
cz bell352 x12
T 2
cnot bell354 2
H bell354
measure bell354
cz bell354 x2
T 1
H bell362
cnot bell362 bell363
cnot x12 bell363
measure bell363
cnot bell363 bell362
cnot bell362 1
T* 1
H bell364
cnot bell364 bell365
cnot x2 bell365
measure bell365
cnot bell365 bell364
cnot bell364 1
T 1
cnot bell362 1
T* 1
cnot bell364 1
H 1
T 0
cnot 1 0
T* 0
cnot bell358 0
T 0
cnot 1 0
T* 0
cnot bell358 0
H 0
T x15
H x15
T x15
H bell366
cnot bell366 bell367
cnot 0 bell367
measure bell367
cnot bell367 bell366
cnot bell366 x15
T* x15
H bell368
cnot bell368 bell369
cnot x14 bell369
measure bell369
cnot bell369 bell368
cnot bell368 x15
T x15
cnot bell366 x15
H bell366
measure bell366
cz bell366 0
T* x15
cnot bell368 x15
H bell368
measure bell368
cz bell368 x14
H x15
T 0
H bell370
cnot bell370 bell371
cnot x14 bell371
measure bell371
cnot bell371 bell370
cnot bell370 0
T* 0
cnot bell370 0
H bell370
measure bell370
cz bell370 x14
H 0
T* 0
cnot 1 0
T 0
cnot bell358 0
T* 0
cnot 1 0
T 0
cnot bell358 0
H 1
T* 1
cnot bell362 1
T 1
cnot bell364 1
T* 1
cnot bell362 1
T 1
cnot bell364 1
T 0
cnot bell362 0
T* 0
cnot bell364 0
T 0
cnot bell362 0
T* 0
cnot bell364 0
H 0
T x14
H x14
T x14
H bell372
cnot bell372 bell373
cnot 0 bell373
measure bell373
cnot bell373 bell372
cnot bell372 x14
T* x14
cnot x13 x14
T x14
cnot bell372 x14
H bell372
measure bell372
cz bell372 0
T* x14
cnot x13 x14
H x14
T 0
cnot bell358 0
T* 0
cnot bell358 0
H bell358
measure bell358
cz bell358 x13
H 0
T* 0
cnot bell362 0
T 0
cnot bell364 0
T* 0
cnot bell362 0
H bell362
measure bell362
cz bell362 x12
T 0
cnot bell364 0
H bell364
measure bell364
cz bell364 x2
cnot bell274 x13
T x13
cnot bell274 x13
H bell274
measure bell274
cz bell274 x3
H x13
T x13
H bell374
cnot bell374 bell375
cnot x12 bell375
measure bell375
cnot bell375 bell374
cnot bell374 x13
T* x13
H bell376
cnot bell376 bell377
cnot x2 bell377
measure bell377
cnot bell377 bell376
cnot bell376 x13
T x13
cnot bell374 x13
H bell374
measure bell374
cz bell374 x12
T* x13
cnot bell376 x13
H bell376
measure bell376
cz bell376 x2
H x13
H bell378
cnot bell378 bell379
cnot x2 bell379
measure bell379
cnot bell379 bell378
cnot bell378 x12
H 7
T 7
H bell380
cnot bell380 bell381
cnot x1 bell381
measure bell381
cnot bell381 bell380
cnot bell380 7
T* 7
H bell382
cnot bell382 bell383
cnot x11 bell383
measure bell383
cnot bell383 bell382
cnot bell382 7
T 7
cnot bell380 7
T* 7
cnot bell382 7
H 7
T 6
H bell384
cnot bell384 bell385
cnot 7 bell385
measure bell385
cnot bell385 bell384
cnot bell384 6
T* 6
H bell386
cnot bell386 bell387
cnot x12 bell387
measure bell387
cnot bell387 bell386
cnot bell386 6
T 6
cnot bell384 6
T* 6
cnot bell386 6
H 6
T 5
cnot 6 5
T* 5
H bell388
cnot bell388 bell389
cnot x13 bell389
measure bell389
cnot bell389 bell388
cnot bell388 5
T 5
cnot 6 5
T* 5
cnot bell388 5
H 5
T 4
H bell390
cnot bell390 bell391
cnot 5 bell391
measure bell391
cnot bell391 bell390
cnot bell390 4
T* 4
H bell392
cnot bell392 bell393
cnot x14 bell393
measure bell393
cnot bell393 bell392
cnot bell392 4
T 4
cnot bell390 4
T* 4
cnot bell392 4
H 4
T 3
cnot 4 3
T* 3
H bell394
cnot bell394 bell395
cnot x15 bell395
measure bell395
cnot bell395 bell394
cnot bell394 3
T 3
cnot 4 3
T* 3
cnot bell394 3
H 3
T 2
H bell396
cnot bell396 bell397
cnot 3 bell397
measure bell397
cnot bell397 bell396
cnot bell396 2
T* 2
H bell398
cnot bell398 bell399
cnot x16 bell399
measure bell399
cnot bell399 bell398
cnot bell398 2
T 2
cnot bell396 2
T* 2
cnot bell398 2
H 2
T 1
H bell400
cnot bell400 bell401
cnot 2 bell401
measure bell401
cnot bell401 bell400
cnot bell400 1
T* 1
H bell402
cnot bell402 bell403
cnot x17 bell403
measure bell403
cnot bell403 bell402
cnot bell402 1
T 1
cnot bell400 1
T* 1
cnot bell402 1
H 1
T 0
cnot 1 0
T* 0
H bell404
cnot bell404 bell405
cnot x18 bell405
measure bell405
cnot bell405 bell404
cnot bell404 0
T 0
cnot 1 0
T* 0
cnot bell404 0
H 0
T x20
H bell406
cnot bell406 bell407
cnot 0 bell407
measure bell407
cnot bell407 bell406
cnot bell406 x20
T* x20
cnot x19 x20
T x20
cnot bell406 x20
H bell406
measure bell406
cz bell406 0
T* x20
cnot x19 x20
H x20
T 0
H bell408
cnot bell408 bell409
cnot x19 bell409
measure bell409
cnot bell409 bell408
cnot bell408 0
T* 0
cnot bell408 0
H bell408
measure bell408
cz bell408 x19
H 0
T* 0
cnot 1 0
T 0
cnot bell404 0
T* 0
cnot 1 0
T 0
cnot bell404 0
H bell404
measure bell404
cz bell404 x18
H 1
T* 1
cnot bell400 1
T 1
cnot bell402 1
T* 1
cnot bell400 1
H bell400
measure bell400
cz bell400 2
T 1
cnot bell402 1
H 2
T* 2
cnot bell396 2
T 2
cnot bell398 2
T* 2
cnot bell396 2
H bell396
measure bell396
cz bell396 3
T 2
cnot bell398 2
H bell398
measure bell398
cz bell398 x16
H 3
T* 3
cnot 4 3
T 3
cnot bell394 3
T* 3
cnot 4 3
T 3
cnot bell394 3
H bell394
measure bell394
cz bell394 x15
H 4
T* 4
cnot bell390 4
T 4
cnot bell392 4
T* 4
cnot bell390 4
H bell390
measure bell390
cz bell390 5
T 4
cnot bell392 4
H 5
T* 5
cnot 6 5
T 5
cnot bell388 5
T* 5
cnot 6 5
T 5
cnot bell388 5
H bell388
measure bell388
cz bell388 x13
H 6
T* 6
cnot bell384 6
T 6
cnot bell386 6
T* 6
cnot bell384 6
H bell384
measure bell384
cz bell384 7
T 6
cnot bell386 6
H 7
T* 7
cnot bell380 7
T 7
cnot bell382 7
T* 7
cnot bell380 7
H bell380
measure bell380
cz bell380 x1
T 7
cnot bell382 7
H bell382
measure bell382
cz bell382 x11
H 7
T 6
H bell410
cnot bell410 bell411
cnot x1 bell411
measure bell411
cnot bell411 bell410
cnot bell410 6
T* 6
H bell412
cnot bell412 bell413
cnot x11 bell413
measure bell413
cnot bell413 bell412
cnot bell412 6
T 6
cnot bell410 6
T* 6
cnot bell412 6
H 6
T 5
cnot 6 5
T* 5
cnot bell386 5
T 5
cnot 6 5
T* 5
cnot bell386 5
H 5
T 4
H bell414
cnot bell414 bell415
cnot 5 bell415
measure bell415
cnot bell415 bell414
cnot bell414 4
T* 4
H bell416
cnot bell416 bell417
cnot x13 bell417
measure bell417
cnot bell417 bell416
cnot bell416 4
T 4
cnot bell414 4
T* 4
cnot bell416 4
H 4
T 3
cnot 4 3
T* 3
cnot bell392 3
T 3
cnot 4 3
T* 3
cnot bell392 3
H 3
T 2
H bell418
cnot bell418 bell419
cnot 3 bell419
measure bell419
cnot bell419 bell418
cnot bell418 2
T* 2
H bell420
cnot bell420 bell421
cnot x15 bell421
measure bell421
cnot bell421 bell420
cnot bell420 2
T 2
cnot bell418 2
T* 2
cnot bell420 2
H 2
T 1
H bell422
cnot bell422 bell423
cnot 2 bell423
measure bell423
cnot bell423 bell422
cnot bell422 1
T* 1
H bell424
cnot bell424 bell425
cnot x16 bell425
measure bell425
cnot bell425 bell424
cnot bell424 1
T 1
cnot bell422 1
T* 1
cnot bell424 1
H 1
T 0
cnot 1 0
T* 0
cnot bell402 0
T 0
cnot 1 0
T* 0
cnot bell402 0
H 0
T x19
H x19
T x19
H bell426
cnot bell426 bell427
cnot 0 bell427
measure bell427
cnot bell427 bell426
cnot bell426 x19
T* x19
H bell428
cnot bell428 bell429
cnot x18 bell429
measure bell429
cnot bell429 bell428
cnot bell428 x19
T x19
cnot bell426 x19
H bell426
measure bell426
cz bell426 0
T* x19
cnot bell428 x19
H bell428
measure bell428
cz bell428 x18
H x19
T 0
H bell430
cnot bell430 bell431
cnot x18 bell431
measure bell431
cnot bell431 bell430
cnot bell430 0
T* 0
cnot bell430 0
H bell430
measure bell430
cz bell430 x18
H 0
T* 0
cnot 1 0
T 0
cnot bell402 0
T* 0
cnot 1 0
T 0
cnot bell402 0
H bell402
measure bell402
cz bell402 x17
H 1
T* 1
cnot bell422 1
T 1
cnot bell424 1
T* 1
cnot bell422 1
H bell422
measure bell422
cz bell422 2
T 1
cnot bell424 1
H 2
T* 2
cnot bell418 2
T 2
cnot bell420 2
T* 2
cnot bell418 2
H bell418
measure bell418
cz bell418 3
T 2
cnot bell420 2
H bell420
measure bell420
cz bell420 x15
H 3
T* 3
cnot 4 3
T 3
cnot bell392 3
T* 3
cnot 4 3
T 3
cnot bell392 3
H bell392
measure bell392
cz bell392 x14
H 4
T* 4
cnot bell414 4
T 4
cnot bell416 4
T* 4
cnot bell414 4
H bell414
measure bell414
cz bell414 5
T 4
cnot bell416 4
H 5
T* 5
cnot 6 5
T 5
cnot bell386 5
T* 5
cnot 6 5
T 5
cnot bell386 5
H bell386
measure bell386
cz bell386 x12
H 6
T* 6
cnot bell410 6
T 6
cnot bell412 6
T* 6
cnot bell410 6
T 6
cnot bell412 6
H 6
T 5
cnot bell410 5
T* 5
cnot bell412 5
T 5
cnot bell410 5
T* 5
cnot bell412 5
H 5
T 4
H bell432
cnot bell432 bell433
cnot 5 bell433
measure bell433
cnot bell433 bell432
cnot bell432 4
T* 4
H bell434
cnot bell434 bell435
cnot x12 bell435
measure bell435
cnot bell435 bell434
cnot bell434 4
T 4
cnot bell432 4
T* 4
cnot bell434 4
H 4
T 3
cnot 4 3
T* 3
cnot bell416 3
T 3
cnot 4 3
T* 3
cnot bell416 3
H 3
T 2
H bell436
cnot bell436 bell437
cnot 3 bell437
measure bell437
cnot bell437 bell436
cnot bell436 2
T* 2
H bell438
cnot bell438 bell439
cnot x14 bell439
measure bell439
cnot bell439 bell438
cnot bell438 2
T 2
cnot bell436 2
T* 2
cnot bell438 2
H 2
T 1
H bell440
cnot bell440 bell441
cnot 2 bell441
measure bell441
cnot bell441 bell440
cnot bell440 1
T* 1
H bell442
cnot bell442 bell443
cnot x15 bell443
measure bell443
cnot bell443 bell442
cnot bell442 1
T 1
cnot bell440 1
T* 1
cnot bell442 1
H 1
T 0
cnot 1 0
T* 0
cnot bell424 0
T 0
cnot 1 0
T* 0
cnot bell424 0
H 0
T x18
H x18
T x18
H bell444
cnot bell444 bell445
cnot 0 bell445
measure bell445
cnot bell445 bell444
cnot bell444 x18
T* x18
H bell446
cnot bell446 bell447
cnot x17 bell447
measure bell447
cnot bell447 bell446
cnot bell446 x18
T x18
cnot bell444 x18
H bell444
measure bell444
cz bell444 0
T* x18
cnot bell446 x18
H bell446
measure bell446
cz bell446 x17
H x18
T 0
H bell448
cnot bell448 bell449
cnot x17 bell449
measure bell449
cnot bell449 bell448
cnot bell448 0
T* 0
cnot bell448 0
H bell448
measure bell448
cz bell448 x17
H 0
T* 0
cnot 1 0
T 0
cnot bell424 0
T* 0
cnot 1 0
T 0
cnot bell424 0
H bell424
measure bell424
cz bell424 x16
H 1
T* 1
cnot bell440 1
T 1
cnot bell442 1
T* 1
cnot bell440 1
H bell440
measure bell440
cz bell440 2
T 1
cnot bell442 1
H 2
T* 2
cnot bell436 2
T 2
cnot bell438 2
T* 2
cnot bell436 2
H bell436
measure bell436
cz bell436 3
T 2
cnot bell438 2
H bell438
measure bell438
cz bell438 x14
H 3
T* 3
cnot 4 3
T 3
cnot bell416 3
T* 3
cnot 4 3
T 3
cnot bell416 3
H bell416
measure bell416
cz bell416 x13
H 4
T* 4
cnot bell432 4
T 4
cnot bell434 4
T* 4
cnot bell432 4
H bell432
measure bell432
cz bell432 5
T 4
cnot bell434 4
H 5
T* 5
cnot bell410 5
T 5
cnot bell412 5
T* 5
cnot bell410 5
H bell410
measure bell410
cz bell410 x1
T 5
cnot bell412 5
H bell412
measure bell412
cz bell412 x11
H 5
T 4
H bell450
cnot bell450 bell451
cnot x1 bell451
measure bell451
cnot bell451 bell450
cnot bell450 4
T* 4
H bell452
cnot bell452 bell453
cnot x11 bell453
measure bell453
cnot bell453 bell452
cnot bell452 4
T 4
cnot bell450 4
T* 4
cnot bell452 4
H 4
T 3
cnot 4 3
T* 3
cnot bell434 3
T 3
cnot 4 3
T* 3
cnot bell434 3
H 3
T 2
H bell454
cnot bell454 bell455
cnot 3 bell455
measure bell455
cnot bell455 bell454
cnot bell454 2
T* 2
H bell456
cnot bell456 bell457
cnot x13 bell457
measure bell457
cnot bell457 bell456
cnot bell456 2
T 2
cnot bell454 2
T* 2
cnot bell456 2
H 2
T 1
H bell458
cnot bell458 bell459
cnot 2 bell459
measure bell459
cnot bell459 bell458
cnot bell458 1
T* 1
H bell460
cnot bell460 bell461
cnot x14 bell461
measure bell461
cnot bell461 bell460
cnot bell460 1
T 1
cnot bell458 1
T* 1
cnot bell460 1
H 1
T 0
cnot 1 0
T* 0
cnot bell442 0
T 0
cnot 1 0
T* 0
cnot bell442 0
H 0
T x17
H x17
T x17
H bell462
cnot bell462 bell463
cnot 0 bell463
measure bell463
cnot bell463 bell462
cnot bell462 x17
T* x17
H bell464
cnot bell464 bell465
cnot x16 bell465
measure bell465
cnot bell465 bell464
cnot bell464 x17
T x17
cnot bell462 x17
H bell462
measure bell462
cz bell462 0
T* x17
cnot bell464 x17
H bell464
measure bell464
cz bell464 x16
H x17
T 0
H bell466
cnot bell466 bell467
cnot x16 bell467
measure bell467
cnot bell467 bell466
cnot bell466 0
T* 0
cnot bell466 0
H bell466
measure bell466
cz bell466 x16
H 0
T* 0
cnot 1 0
T 0
cnot bell442 0
T* 0
cnot 1 0
T 0
cnot bell442 0
H 1
T* 1
cnot bell458 1
T 1
cnot bell460 1
T* 1
cnot bell458 1
H bell458
measure bell458
cz bell458 2
T 1
cnot bell460 1
H 2
T* 2
cnot bell454 2
T 2
cnot bell456 2
T* 2
cnot bell454 2
H bell454
measure bell454
cz bell454 3
T 2
cnot bell456 2
H bell456
measure bell456
cz bell456 x13
H 3
T* 3
cnot 4 3
T 3
cnot bell434 3
T* 3
cnot 4 3
T 3
cnot bell434 3
H bell434
measure bell434
cz bell434 x12
H 4
T* 4
cnot bell450 4
T 4
cnot bell452 4
T* 4
cnot bell450 4
T 4
cnot bell452 4
H 4
T 3
cnot bell450 3
T* 3
cnot bell452 3
T 3
cnot bell450 3
T* 3
cnot bell452 3
H 3
T 2
H bell468
cnot bell468 bell469
cnot 3 bell469
measure bell469
cnot bell469 bell468
cnot bell468 2
T* 2
H bell470
cnot bell470 bell471
cnot x12 bell471
measure bell471
cnot bell471 bell470
cnot bell470 2
T 2
cnot bell468 2
T* 2
cnot bell470 2
H 2
T 1
H bell472
cnot bell472 bell473
cnot 2 bell473
measure bell473
cnot bell473 bell472
cnot bell472 1
T* 1
H bell474
cnot bell474 bell475
cnot x13 bell475
measure bell475
cnot bell475 bell474
cnot bell474 1
T 1
cnot bell472 1
T* 1
cnot bell474 1
H 1
T 0
cnot 1 0
T* 0
cnot bell460 0
T 0
cnot 1 0
T* 0
cnot bell460 0
H 0
T x16
H x16
T x16
H bell476
cnot bell476 bell477
cnot 0 bell477
measure bell477
cnot bell477 bell476
cnot bell476 x16
T* x16
cnot x15 x16
T x16
cnot bell476 x16
H bell476
measure bell476
cz bell476 0
T* x16
cnot x15 x16
H x16
T 0
cnot bell442 0
T* 0
cnot bell442 0
H bell442
measure bell442
cz bell442 x15
H 0
T* 0
cnot 1 0
T 0
cnot bell460 0
T* 0
cnot 1 0
T 0
cnot bell460 0
H bell460
measure bell460
cz bell460 x14
H 1
T* 1
cnot bell472 1
T 1
cnot bell474 1
T* 1
cnot bell472 1
H bell472
measure bell472
cz bell472 2
T 1
cnot bell474 1
H 2
T* 2
cnot bell468 2
T 2
cnot bell470 2
T* 2
cnot bell468 2
H bell468
measure bell468
cz bell468 3
T 2
cnot bell470 2
H bell470
measure bell470
cz bell470 x12
H 3
T* 3
cnot bell450 3
T 3
cnot bell452 3
T* 3
cnot bell450 3
H bell450
measure bell450
cz bell450 x1
T 3
cnot bell452 3
H bell452
measure bell452
cz bell452 x11
H 3
T 2
H bell478
cnot bell478 bell479
cnot x1 bell479
measure bell479
cnot bell479 bell478
cnot bell478 2
T* 2
H bell480
cnot bell480 bell481
cnot x11 bell481
measure bell481
cnot bell481 bell480
cnot bell480 2
T 2
cnot bell478 2
T* 2
cnot bell480 2
H 2
T 1
H bell482
cnot bell482 bell483
cnot 2 bell483
measure bell483
cnot bell483 bell482
cnot bell482 1
T* 1
H bell484
cnot bell484 bell485
cnot x12 bell485
measure bell485
cnot bell485 bell484
cnot bell484 1
T 1
cnot bell482 1
T* 1
cnot bell484 1
H 1
T 0
cnot 1 0
T* 0
cnot bell474 0
T 0
cnot 1 0
T* 0
cnot bell474 0
H 0
T x15
H x15
T x15
H bell486
cnot bell486 bell487
cnot 0 bell487
measure bell487
cnot bell487 bell486
cnot bell486 x15
T* x15
H bell488
cnot bell488 bell489
cnot x14 bell489
measure bell489
cnot bell489 bell488
cnot bell488 x15
T x15
cnot bell486 x15
H bell486
measure bell486
cz bell486 0
T* x15
cnot bell488 x15
H bell488
measure bell488
cz bell488 x14
H x15
T 0
H bell490
cnot bell490 bell491
cnot x14 bell491
measure bell491
cnot bell491 bell490
cnot bell490 0
T* 0
cnot bell490 0
H bell490
measure bell490
cz bell490 x14
H 0
T* 0
cnot 1 0
T 0
cnot bell474 0
T* 0
cnot 1 0
T 0
cnot bell474 0
H 1
T* 1
cnot bell482 1
T 1
cnot bell484 1
T* 1
cnot bell482 1
H bell482
measure bell482
cz bell482 2
T 1
cnot bell484 1
H 2
T* 2
cnot bell478 2
T 2
cnot bell480 2
T* 2
cnot bell478 2
H bell478
measure bell478
cz bell478 x1
T 2
cnot bell480 2
H bell480
measure bell480
cz bell480 x11
H 2
T 1
H bell492
cnot bell492 bell493
cnot x1 bell493
measure bell493
cnot bell493 bell492
cnot bell492 1
T* 1
H bell494
cnot bell494 bell495
cnot x11 bell495
measure bell495
cnot bell495 bell494
cnot bell494 1
T 1
cnot bell492 1
T* 1
cnot bell494 1
H 1
T 0
cnot 1 0
T* 0
cnot bell484 0
T 0
cnot 1 0
T* 0
cnot bell484 0
H 0
T x14
H x14
T x14
H bell496
cnot bell496 bell497
cnot 0 bell497
measure bell497
cnot bell497 bell496
cnot bell496 x14
T* x14
cnot x13 x14
T x14
cnot bell496 x14
H bell496
measure bell496
cz bell496 0
T* x14
cnot x13 x14
H x14
T 0
cnot bell474 0
T* 0
cnot bell474 0
H bell474
measure bell474
cz bell474 x13
H 0
T* 0
cnot 1 0
T 0
cnot bell484 0
T* 0
cnot 1 0
T 0
cnot bell484 0
H bell484
measure bell484
cz bell484 x12
H 1
T* 1
cnot bell492 1
T 1
cnot bell494 1
T* 1
cnot bell492 1
T 1
cnot bell494 1
H 1
T 0
cnot bell492 0
T* 0
cnot bell494 0
T 0
cnot bell492 0
T* 0
cnot bell494 0
H 0
T x13
H x13
T x13
H bell498
cnot bell498 bell499
cnot 0 bell499
measure bell499
cnot bell499 bell498
cnot bell498 x13
T* x13
H bell500
cnot bell500 bell501
cnot x12 bell501
measure bell501
cnot bell501 bell500
cnot bell500 x13
T x13
cnot bell498 x13
H bell498
measure bell498
cz bell498 0
T* x13
cnot bell500 x13
H bell500
measure bell500
cz bell500 x12
H x13
T 0
H bell502
cnot bell502 bell503
cnot x12 bell503
measure bell503
cnot bell503 bell502
cnot bell502 0
T* 0
cnot bell502 0
H bell502
measure bell502
cz bell502 x12
H 0
T* 0
cnot bell492 0
T 0
cnot bell494 0
T* 0
cnot bell492 0
H bell492
measure bell492
cz bell492 x1
T 0
cnot bell494 0
H bell494
measure bell494
cz bell494 x11
H 0
cnot bell378 x12
T x12
cnot bell378 x12
H bell378
measure bell378
cz bell378 x2
H x12
T x12
H bell504
cnot bell504 bell505
cnot x1 bell505
measure bell505
cnot bell505 bell504
cnot bell504 x12
T* x12
H bell506
cnot bell506 bell507
cnot x11 bell507
measure bell507
cnot bell507 bell506
cnot bell506 x12
T x12
cnot bell504 x12
H bell504
measure bell504
cz bell504 x1
T* x12
cnot bell506 x12
H bell506
measure bell506
cz bell506 x11
H x12
T x1
T x11
cnot x1 x11
T* x11
T x2
T x3
T x4
T x5
T x6
T x7
T x8
T x9
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
reset bell484
reset bell485
reset bell486
reset bell487
reset bell488
reset bell489
reset bell490
reset bell491
reset bell492
reset bell493
reset bell494
reset bell495
reset bell496
reset bell497
reset bell498
reset bell499
reset bell500
reset bell501
reset bell502
reset bell503
reset bell504
reset bell505
reset bell506
reset bell507
END
