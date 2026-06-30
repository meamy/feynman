# Hyperedge cut (ebits): 54

# Actual ebits used (Synthesis): 373
# Distribution Verification: PASS

# Feynman -- quantum circuit toolkit
# Original (benchmarks/qc/gf2^10_mult.qc):
#   Qubits: 30
#   H: 38
#   T: 700
#   cnot: 609
#   Depth: 246
#   T depth: 119
# Result (103.161ms):
#   Qubits: 776
#   H: 784
#   S: 25
#   T: 410
#   Z: 6
#   cnot: 1771
#   cz: 375
#   measure: 746
#   reset: 748
#   Depth: 619
#   T depth: 109


# Result Circuit
.v a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 bell0 bell1 bell10 bell100 bell101 bell102 bell103 bell104 bell105 bell106 bell107 bell108 bell109 bell11 bell110 bell111 bell112 bell113 bell114 bell115 bell116 bell117 bell118 bell119 bell12 bell120 bell121 bell122 bell123 bell124 bell125 bell126 bell127 bell128 bell129 bell13 bell130 bell131 bell132 bell133 bell134 bell135 bell136 bell137 bell138 bell139 bell14 bell140 bell141 bell142 bell143 bell144 bell145 bell146 bell147 bell148 bell149 bell15 bell150 bell151 bell152 bell153 bell154 bell155 bell156 bell157 bell158 bell159 bell16 bell160 bell161 bell162 bell163 bell164 bell165 bell166 bell167 bell168 bell169 bell17 bell170 bell171 bell172 bell173 bell174 bell175 bell176 bell177 bell178 bell179 bell18 bell180 bell181 bell182 bell183 bell184 bell185 bell186 bell187 bell188 bell189 bell19 bell190 bell191 bell192 bell193 bell194 bell195 bell196 bell197 bell198 bell199 bell2 bell20 bell200 bell201 bell202 bell203 bell204 bell205 bell206 bell207 bell208 bell209 bell21 bell210 bell211 bell212 bell213 bell214 bell215 bell216 bell217 bell218 bell219 bell22 bell220 bell221 bell222 bell223 bell224 bell225 bell226 bell227 bell228 bell229 bell23 bell230 bell231 bell232 bell233 bell234 bell235 bell236 bell237 bell238 bell239 bell24 bell240 bell241 bell242 bell243 bell244 bell245 bell246 bell247 bell248 bell249 bell25 bell250 bell251 bell252 bell253 bell254 bell255 bell256 bell257 bell258 bell259 bell26 bell260 bell261 bell262 bell263 bell264 bell265 bell266 bell267 bell268 bell269 bell27 bell270 bell271 bell272 bell273 bell274 bell275 bell276 bell277 bell278 bell279 bell28 bell280 bell281 bell282 bell283 bell284 bell285 bell286 bell287 bell288 bell289 bell29 bell290 bell291 bell292 bell293 bell294 bell295 bell296 bell297 bell298 bell299 bell3 bell30 bell300 bell301 bell302 bell303 bell304 bell305 bell306 bell307 bell308 bell309 bell31 bell310 bell311 bell312 bell313 bell314 bell315 bell316 bell317 bell318 bell319 bell32 bell320 bell321 bell322 bell323 bell324 bell325 bell326 bell327 bell328 bell329 bell33 bell330 bell331 bell332 bell333 bell334 bell335 bell336 bell337 bell338 bell339 bell34 bell340 bell341 bell342 bell343 bell344 bell345 bell346 bell347 bell348 bell349 bell35 bell350 bell351 bell352 bell353 bell354 bell355 bell356 bell357 bell358 bell359 bell36 bell360 bell361 bell362 bell363 bell364 bell365 bell366 bell367 bell368 bell369 bell37 bell370 bell371 bell372 bell373 bell374 bell375 bell376 bell377 bell378 bell379 bell38 bell380 bell381 bell382 bell383 bell384 bell385 bell386 bell387 bell388 bell389 bell39 bell390 bell391 bell392 bell393 bell394 bell395 bell396 bell397 bell398 bell399 bell4 bell40 bell400 bell401 bell402 bell403 bell404 bell405 bell406 bell407 bell408 bell409 bell41 bell410 bell411 bell412 bell413 bell414 bell415 bell416 bell417 bell418 bell419 bell42 bell420 bell421 bell422 bell423 bell424 bell425 bell426 bell427 bell428 bell429 bell43 bell430 bell431 bell432 bell433 bell434 bell435 bell436 bell437 bell438 bell439 bell44 bell440 bell441 bell442 bell443 bell444 bell445 bell446 bell447 bell448 bell449 bell45 bell450 bell451 bell452 bell453 bell454 bell455 bell456 bell457 bell458 bell459 bell46 bell460 bell461 bell462 bell463 bell464 bell465 bell466 bell467 bell468 bell469 bell47 bell470 bell471 bell472 bell473 bell474 bell475 bell476 bell477 bell478 bell479 bell48 bell480 bell481 bell482 bell483 bell484 bell485 bell486 bell487 bell488 bell489 bell49 bell490 bell491 bell492 bell493 bell494 bell495 bell496 bell497 bell498 bell499 bell5 bell50 bell500 bell501 bell502 bell503 bell504 bell505 bell506 bell507 bell508 bell509 bell51 bell510 bell511 bell512 bell513 bell514 bell515 bell516 bell517 bell518 bell519 bell52 bell520 bell521 bell522 bell523 bell524 bell525 bell526 bell527 bell528 bell529 bell53 bell530 bell531 bell532 bell533 bell534 bell535 bell536 bell537 bell538 bell539 bell54 bell540 bell541 bell542 bell543 bell544 bell545 bell546 bell547 bell548 bell549 bell55 bell550 bell551 bell552 bell553 bell554 bell555 bell556 bell557 bell558 bell559 bell56 bell560 bell561 bell562 bell563 bell564 bell565 bell566 bell567 bell568 bell569 bell57 bell570 bell571 bell572 bell573 bell574 bell575 bell576 bell577 bell578 bell579 bell58 bell580 bell581 bell582 bell583 bell584 bell585 bell586 bell587 bell588 bell589 bell59 bell590 bell591 bell592 bell593 bell594 bell595 bell596 bell597 bell598 bell599 bell6 bell60 bell600 bell601 bell602 bell603 bell604 bell605 bell606 bell607 bell608 bell609 bell61 bell610 bell611 bell612 bell613 bell614 bell615 bell616 bell617 bell618 bell619 bell62 bell620 bell621 bell622 bell623 bell624 bell625 bell626 bell627 bell628 bell629 bell63 bell630 bell631 bell632 bell633 bell634 bell635 bell636 bell637 bell638 bell639 bell64 bell640 bell641 bell642 bell643 bell644 bell645 bell646 bell647 bell648 bell649 bell65 bell650 bell651 bell652 bell653 bell654 bell655 bell656 bell657 bell658 bell659 bell66 bell660 bell661 bell662 bell663 bell664 bell665 bell666 bell667 bell668 bell669 bell67 bell670 bell671 bell672 bell673 bell674 bell675 bell676 bell677 bell678 bell679 bell68 bell680 bell681 bell682 bell683 bell684 bell685 bell686 bell687 bell688 bell689 bell69 bell690 bell691 bell692 bell693 bell694 bell695 bell696 bell697 bell698 bell699 bell7 bell70 bell700 bell701 bell702 bell703 bell704 bell705 bell706 bell707 bell708 bell709 bell71 bell710 bell711 bell712 bell713 bell714 bell715 bell716 bell717 bell718 bell719 bell72 bell720 bell721 bell722 bell723 bell724 bell725 bell726 bell727 bell728 bell729 bell73 bell730 bell731 bell732 bell733 bell734 bell735 bell736 bell737 bell738 bell739 bell74 bell740 bell741 bell742 bell743 bell744 bell745 bell75 bell76 bell77 bell78 bell79 bell8 bell80 bell81 bell82 bell83 bell84 bell85 bell86 bell87 bell88 bell89 bell9 bell90 bell91 bell92 bell93 bell94 bell95 bell96 bell97 bell98 bell99
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
H bell120
measure bell120
cz bell120 a9
T* c4
H bell124
cnot bell124 bell125
cnot a8 bell125
measure bell125
cnot bell125 bell124
cnot bell124 c4
cnot bell122 c4
H bell122
measure bell122
cz bell122 b5
T* c4
H bell126
cnot bell126 bell127
cnot b6 bell127
measure bell127
cnot bell127 bell126
cnot bell126 c4
T c4
cnot bell124 c4
H bell124
measure bell124
cz bell124 a8
T* c4
H bell128
cnot bell128 bell129
cnot a7 bell129
measure bell129
cnot bell129 bell128
cnot bell128 c4
cnot bell126 c4
H bell126
measure bell126
cz bell126 b6
T* c4
H bell130
cnot bell130 bell131
cnot b7 bell131
measure bell131
cnot bell131 bell130
cnot bell130 c4
T c4
cnot bell128 c4
H bell128
measure bell128
cz bell128 a7
T* c4
H bell132
cnot bell132 bell133
cnot a6 bell133
measure bell133
cnot bell133 bell132
cnot bell132 c4
cnot bell130 c4
H bell130
measure bell130
cz bell130 b7
T* c4
H bell134
cnot bell134 bell135
cnot b8 bell135
measure bell135
cnot bell135 bell134
cnot bell134 c4
T c4
cnot bell132 c4
H bell132
measure bell132
cz bell132 a6
T* c4
H bell136
cnot bell136 bell137
cnot a5 bell137
measure bell137
cnot bell137 bell136
cnot bell136 c4
cnot bell134 c4
H bell134
measure bell134
cz bell134 b8
T* c4
H bell138
cnot bell138 bell139
cnot b9 bell139
measure bell139
cnot bell139 bell138
cnot bell138 c4
T c4
cnot bell136 c4
H bell136
measure bell136
cz bell136 a5
T* c4
cnot bell138 c4
H bell138
measure bell138
cz bell138 b9
H c4
Z c5
H bell140
cnot bell140 bell141
cnot a9 bell141
measure bell141
cnot bell141 bell140
cnot bell140 c5
T* c5
H bell142
cnot bell142 bell143
cnot b6 bell143
measure bell143
cnot bell143 bell142
cnot bell142 c5
T c5
cnot bell140 c5
H bell140
measure bell140
cz bell140 a9
T* c5
H bell144
cnot bell144 bell145
cnot a8 bell145
measure bell145
cnot bell145 bell144
cnot bell144 c5
cnot bell142 c5
H bell142
measure bell142
cz bell142 b6
T* c5
H bell146
cnot bell146 bell147
cnot b7 bell147
measure bell147
cnot bell147 bell146
cnot bell146 c5
T c5
cnot bell144 c5
H bell144
measure bell144
cz bell144 a8
T* c5
H bell148
cnot bell148 bell149
cnot a7 bell149
measure bell149
cnot bell149 bell148
cnot bell148 c5
cnot bell146 c5
H bell146
measure bell146
cz bell146 b7
T* c5
H bell150
cnot bell150 bell151
cnot b8 bell151
measure bell151
cnot bell151 bell150
cnot bell150 c5
T c5
cnot bell148 c5
H bell148
measure bell148
cz bell148 a7
T* c5
H bell152
cnot bell152 bell153
cnot a6 bell153
measure bell153
cnot bell153 bell152
cnot bell152 c5
cnot bell150 c5
H bell150
measure bell150
cz bell150 b8
T* c5
H bell154
cnot bell154 bell155
cnot b9 bell155
measure bell155
cnot bell155 bell154
cnot bell154 c5
T c5
cnot bell152 c5
H bell152
measure bell152
cz bell152 a6
T* c5
cnot bell154 c5
H bell154
measure bell154
cz bell154 b9
H c5
T* c6
Z c6
H bell156
cnot bell156 bell157
cnot a9 bell157
measure bell157
cnot bell157 bell156
cnot bell156 c6
T* c6
H bell158
cnot bell158 bell159
cnot b7 bell159
measure bell159
cnot bell159 bell158
cnot bell158 c6
T c6
cnot bell156 c6
H bell156
measure bell156
cz bell156 a9
T* c6
H bell160
cnot bell160 bell161
cnot a8 bell161
measure bell161
cnot bell161 bell160
cnot bell160 c6
cnot bell158 c6
H bell158
measure bell158
cz bell158 b7
T* c6
H bell162
cnot bell162 bell163
cnot b8 bell163
measure bell163
cnot bell163 bell162
cnot bell162 c6
T c6
cnot bell160 c6
H bell160
measure bell160
cz bell160 a8
T* c6
H bell164
cnot bell164 bell165
cnot a7 bell165
measure bell165
cnot bell165 bell164
cnot bell164 c6
cnot bell162 c6
H bell162
measure bell162
cz bell162 b8
T* c6
H bell166
cnot bell166 bell167
cnot b9 bell167
measure bell167
cnot bell167 bell166
cnot bell166 c6
T c6
cnot bell164 c6
H bell164
measure bell164
cz bell164 a7
T* c6
cnot bell166 c6
H bell166
measure bell166
cz bell166 b9
H c6
S c7
H bell168
cnot bell168 bell169
cnot a9 bell169
measure bell169
cnot bell169 bell168
cnot bell168 c7
T* c7
H bell170
cnot bell170 bell171
cnot b8 bell171
measure bell171
cnot bell171 bell170
cnot bell170 c7
T c7
cnot bell168 c7
H bell168
measure bell168
cz bell168 a9
T* c7
H bell172
cnot bell172 bell173
cnot a8 bell173
measure bell173
cnot bell173 bell172
cnot bell172 c7
cnot bell170 c7
H bell170
measure bell170
cz bell170 b8
T* c7
H bell174
cnot bell174 bell175
cnot b9 bell175
measure bell175
cnot bell175 bell174
cnot bell174 c7
T c7
cnot bell172 c7
H bell172
measure bell172
cz bell172 a8
T* c7
cnot bell174 c7
H bell174
measure bell174
cz bell174 b9
H c7
T c8
H bell176
cnot bell176 bell177
cnot a9 bell177
measure bell177
cnot bell177 bell176
cnot bell176 c8
T* c8
H bell178
cnot bell178 bell179
cnot b9 bell179
measure bell179
cnot bell179 bell178
cnot bell178 c8
T c8
cnot bell176 c8
H bell176
measure bell176
cz bell176 a9
T* c8
cnot bell178 c8
H bell178
measure bell178
cz bell178 b9
H c8
H bell180
cnot bell180 bell181
cnot c7 bell181
measure bell181
cnot bell181 bell180
cnot bell180 c0
H bell180
measure bell180
cz bell180 c7
cnot c8 c1
H bell182
cnot bell182 bell183
cnot c6 bell183
measure bell183
cnot bell183 bell182
cnot bell182 c9
H bell182
measure bell182
cz bell182 c6
H bell184
cnot bell184 bell185
cnot c5 bell185
measure bell185
cnot bell185 bell184
cnot bell184 c8
H bell184
measure bell184
cz bell184 c5
cnot c4 c7
cnot c3 c6
cnot c2 c5
H bell186
cnot bell186 bell187
cnot c1 bell187
measure bell187
cnot bell187 bell186
cnot bell186 c4
H bell186
measure bell186
cz bell186 c1
H bell188
cnot bell188 bell189
cnot c0 bell189
measure bell189
cnot bell189 bell188
cnot bell188 c3
H bell188
measure bell188
cz bell188 c0
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
cnot a0 c0
T* c0
H bell190
cnot bell190 bell191
cnot b0 bell191
measure bell191
cnot bell191 bell190
cnot bell190 c0
T c0
cnot a0 c0
T* c0
cnot bell190 c0
H bell190
measure bell190
cz bell190 b0
H c0
S c1
H bell192
cnot bell192 bell193
cnot a1 bell193
measure bell193
cnot bell193 bell192
cnot bell192 c1
T* c1
H bell194
cnot bell194 bell195
cnot b0 bell195
measure bell195
cnot bell195 bell194
cnot bell194 c1
T c1
cnot bell192 c1
H bell192
measure bell192
cz bell192 a1
T* c1
H bell196
cnot bell196 bell197
cnot a0 bell197
measure bell197
cnot bell197 bell196
cnot bell196 c1
cnot bell194 c1
H bell194
measure bell194
cz bell194 b0
T* c1
H bell198
cnot bell198 bell199
cnot b1 bell199
measure bell199
cnot bell199 bell198
cnot bell198 c1
T c1
cnot bell196 c1
H bell196
measure bell196
cz bell196 a0
T* c1
cnot bell198 c1
H bell198
measure bell198
cz bell198 b1
H c1
T* c2
Z c2
H bell200
cnot bell200 bell201
cnot a2 bell201
measure bell201
cnot bell201 bell200
cnot bell200 c2
T* c2
H bell202
cnot bell202 bell203
cnot b0 bell203
measure bell203
cnot bell203 bell202
cnot bell202 c2
T c2
cnot bell200 c2
H bell200
measure bell200
cz bell200 a2
T* c2
H bell204
cnot bell204 bell205
cnot a1 bell205
measure bell205
cnot bell205 bell204
cnot bell204 c2
cnot bell202 c2
H bell202
measure bell202
cz bell202 b0
T* c2
H bell206
cnot bell206 bell207
cnot b1 bell207
measure bell207
cnot bell207 bell206
cnot bell206 c2
T c2
cnot bell204 c2
H bell204
measure bell204
cz bell204 a1
T* c2
H bell208
cnot bell208 bell209
cnot a0 bell209
measure bell209
cnot bell209 bell208
cnot bell208 c2
cnot bell206 c2
H bell206
measure bell206
cz bell206 b1
T* c2
H bell210
cnot bell210 bell211
cnot b2 bell211
measure bell211
cnot bell211 bell210
cnot bell210 c2
T c2
cnot bell208 c2
H bell208
measure bell208
cz bell208 a0
T* c2
cnot bell210 c2
H bell210
measure bell210
cz bell210 b2
H c2
Z c3
H bell212
cnot bell212 bell213
cnot a3 bell213
measure bell213
cnot bell213 bell212
cnot bell212 c3
T* c3
H bell214
cnot bell214 bell215
cnot b0 bell215
measure bell215
cnot bell215 bell214
cnot bell214 c3
T c3
cnot bell212 c3
H bell212
measure bell212
cz bell212 a3
T* c3
H bell216
cnot bell216 bell217
cnot a2 bell217
measure bell217
cnot bell217 bell216
cnot bell216 c3
cnot bell214 c3
H bell214
measure bell214
cz bell214 b0
T* c3
H bell218
cnot bell218 bell219
cnot b1 bell219
measure bell219
cnot bell219 bell218
cnot bell218 c3
T c3
cnot bell216 c3
H bell216
measure bell216
cz bell216 a2
T* c3
H bell220
cnot bell220 bell221
cnot a1 bell221
measure bell221
cnot bell221 bell220
cnot bell220 c3
cnot bell218 c3
H bell218
measure bell218
cz bell218 b1
T* c3
H bell222
cnot bell222 bell223
cnot b2 bell223
measure bell223
cnot bell223 bell222
cnot bell222 c3
T c3
cnot bell220 c3
H bell220
measure bell220
cz bell220 a1
T* c3
H bell224
cnot bell224 bell225
cnot a0 bell225
measure bell225
cnot bell225 bell224
cnot bell224 c3
cnot bell222 c3
H bell222
measure bell222
cz bell222 b2
T* c3
H bell226
cnot bell226 bell227
cnot b3 bell227
measure bell227
cnot bell227 bell226
cnot bell226 c3
T c3
cnot bell224 c3
H bell224
measure bell224
cz bell224 a0
T* c3
cnot bell226 c3
H bell226
measure bell226
cz bell226 b3
H c3
T c4
Z c4
H bell228
cnot bell228 bell229
cnot a4 bell229
measure bell229
cnot bell229 bell228
cnot bell228 c4
T* c4
H bell230
cnot bell230 bell231
cnot b0 bell231
measure bell231
cnot bell231 bell230
cnot bell230 c4
T c4
cnot bell228 c4
H bell228
measure bell228
cz bell228 a4
T* c4
H bell232
cnot bell232 bell233
cnot a3 bell233
measure bell233
cnot bell233 bell232
cnot bell232 c4
cnot bell230 c4
H bell230
measure bell230
cz bell230 b0
T* c4
H bell234
cnot bell234 bell235
cnot b1 bell235
measure bell235
cnot bell235 bell234
cnot bell234 c4
T c4
cnot bell232 c4
H bell232
measure bell232
cz bell232 a3
T* c4
H bell236
cnot bell236 bell237
cnot a2 bell237
measure bell237
cnot bell237 bell236
cnot bell236 c4
cnot bell234 c4
H bell234
measure bell234
cz bell234 b1
T* c4
H bell238
cnot bell238 bell239
cnot b2 bell239
measure bell239
cnot bell239 bell238
cnot bell238 c4
T c4
cnot bell236 c4
H bell236
measure bell236
cz bell236 a2
T* c4
H bell240
cnot bell240 bell241
cnot a1 bell241
measure bell241
cnot bell241 bell240
cnot bell240 c4
cnot bell238 c4
H bell238
measure bell238
cz bell238 b2
T* c4
H bell242
cnot bell242 bell243
cnot b3 bell243
measure bell243
cnot bell243 bell242
cnot bell242 c4
T c4
cnot bell240 c4
H bell240
measure bell240
cz bell240 a1
T* c4
H bell244
cnot bell244 bell245
cnot a0 bell245
measure bell245
cnot bell245 bell244
cnot bell244 c4
cnot bell242 c4
H bell242
measure bell242
cz bell242 b3
T* c4
H bell246
cnot bell246 bell247
cnot b4 bell247
measure bell247
cnot bell247 bell246
cnot bell246 c4
T c4
cnot bell244 c4
H bell244
measure bell244
cz bell244 a0
T* c4
cnot bell246 c4
H bell246
measure bell246
cz bell246 b4
H c4
S* c5
H bell248
cnot bell248 bell249
cnot a5 bell249
measure bell249
cnot bell249 bell248
cnot bell248 c5
T* c5
H bell250
cnot bell250 bell251
cnot b0 bell251
measure bell251
cnot bell251 bell250
cnot bell250 c5
T c5
cnot bell248 c5
H bell248
measure bell248
cz bell248 a5
T* c5
H bell252
cnot bell252 bell253
cnot a4 bell253
measure bell253
cnot bell253 bell252
cnot bell252 c5
cnot bell250 c5
H bell250
measure bell250
cz bell250 b0
T* c5
H bell254
cnot bell254 bell255
cnot b1 bell255
measure bell255
cnot bell255 bell254
cnot bell254 c5
T c5
cnot bell252 c5
H bell252
measure bell252
cz bell252 a4
T* c5
H bell256
cnot bell256 bell257
cnot a3 bell257
measure bell257
cnot bell257 bell256
cnot bell256 c5
cnot bell254 c5
H bell254
measure bell254
cz bell254 b1
T* c5
H bell258
cnot bell258 bell259
cnot b2 bell259
measure bell259
cnot bell259 bell258
cnot bell258 c5
T c5
cnot bell256 c5
H bell256
measure bell256
cz bell256 a3
T* c5
H bell260
cnot bell260 bell261
cnot a2 bell261
measure bell261
cnot bell261 bell260
cnot bell260 c5
cnot bell258 c5
H bell258
measure bell258
cz bell258 b2
T* c5
H bell262
cnot bell262 bell263
cnot b3 bell263
measure bell263
cnot bell263 bell262
cnot bell262 c5
T c5
cnot bell260 c5
H bell260
measure bell260
cz bell260 a2
T* c5
H bell264
cnot bell264 bell265
cnot a1 bell265
measure bell265
cnot bell265 bell264
cnot bell264 c5
cnot bell262 c5
H bell262
measure bell262
cz bell262 b3
T* c5
H bell266
cnot bell266 bell267
cnot b4 bell267
measure bell267
cnot bell267 bell266
cnot bell266 c5
T c5
cnot bell264 c5
H bell264
measure bell264
cz bell264 a1
T* c5
H bell268
cnot bell268 bell269
cnot a0 bell269
measure bell269
cnot bell269 bell268
cnot bell268 c5
cnot bell266 c5
H bell266
measure bell266
cz bell266 b4
T* c5
H bell270
cnot bell270 bell271
cnot b5 bell271
measure bell271
cnot bell271 bell270
cnot bell270 c5
T c5
cnot bell268 c5
H bell268
measure bell268
cz bell268 a0
T* c5
cnot bell270 c5
H bell270
measure bell270
cz bell270 b5
H c5
T* c6
H bell272
cnot bell272 bell273
cnot a6 bell273
measure bell273
cnot bell273 bell272
cnot bell272 c6
T* c6
H bell274
cnot bell274 bell275
cnot b0 bell275
measure bell275
cnot bell275 bell274
cnot bell274 c6
T c6
cnot bell272 c6
H bell272
measure bell272
cz bell272 a6
T* c6
H bell276
cnot bell276 bell277
cnot a5 bell277
measure bell277
cnot bell277 bell276
cnot bell276 c6
cnot bell274 c6
H bell274
measure bell274
cz bell274 b0
T* c6
H bell278
cnot bell278 bell279
cnot b1 bell279
measure bell279
cnot bell279 bell278
cnot bell278 c6
T c6
cnot bell276 c6
H bell276
measure bell276
cz bell276 a5
T* c6
H bell280
cnot bell280 bell281
cnot a4 bell281
measure bell281
cnot bell281 bell280
cnot bell280 c6
cnot bell278 c6
H bell278
measure bell278
cz bell278 b1
T* c6
H bell282
cnot bell282 bell283
cnot b2 bell283
measure bell283
cnot bell283 bell282
cnot bell282 c6
T c6
cnot bell280 c6
H bell280
measure bell280
cz bell280 a4
T* c6
H bell284
cnot bell284 bell285
cnot a3 bell285
measure bell285
cnot bell285 bell284
cnot bell284 c6
cnot bell282 c6
H bell282
measure bell282
cz bell282 b2
T* c6
H bell286
cnot bell286 bell287
cnot b3 bell287
measure bell287
cnot bell287 bell286
cnot bell286 c6
T c6
cnot bell284 c6
H bell284
measure bell284
cz bell284 a3
T* c6
H bell288
cnot bell288 bell289
cnot a2 bell289
measure bell289
cnot bell289 bell288
cnot bell288 c6
cnot bell286 c6
H bell286
measure bell286
cz bell286 b3
T* c6
H bell290
cnot bell290 bell291
cnot b4 bell291
measure bell291
cnot bell291 bell290
cnot bell290 c6
T c6
cnot bell288 c6
H bell288
measure bell288
cz bell288 a2
T* c6
H bell292
cnot bell292 bell293
cnot a1 bell293
measure bell293
cnot bell293 bell292
cnot bell292 c6
cnot bell290 c6
H bell290
measure bell290
cz bell290 b4
T* c6
H bell294
cnot bell294 bell295
cnot b5 bell295
measure bell295
cnot bell295 bell294
cnot bell294 c6
T c6
cnot bell292 c6
H bell292
measure bell292
cz bell292 a1
T* c6
H bell296
cnot bell296 bell297
cnot a0 bell297
measure bell297
cnot bell297 bell296
cnot bell296 c6
cnot bell294 c6
H bell294
measure bell294
cz bell294 b5
T* c6
H bell298
cnot bell298 bell299
cnot b6 bell299
measure bell299
cnot bell299 bell298
cnot bell298 c6
T c6
cnot bell296 c6
H bell296
measure bell296
cz bell296 a0
T* c6
cnot bell298 c6
H bell298
measure bell298
cz bell298 b6
H c6
H bell300
cnot bell300 bell301
cnot a7 bell301
measure bell301
cnot bell301 bell300
cnot bell300 c7
T* c7
H bell302
cnot bell302 bell303
cnot b0 bell303
measure bell303
cnot bell303 bell302
cnot bell302 c7
T c7
cnot bell300 c7
H bell300
measure bell300
cz bell300 a7
T* c7
H bell304
cnot bell304 bell305
cnot a6 bell305
measure bell305
cnot bell305 bell304
cnot bell304 c7
cnot bell302 c7
H bell302
measure bell302
cz bell302 b0
T* c7
H bell306
cnot bell306 bell307
cnot b1 bell307
measure bell307
cnot bell307 bell306
cnot bell306 c7
T c7
cnot bell304 c7
H bell304
measure bell304
cz bell304 a6
T* c7
H bell308
cnot bell308 bell309
cnot a5 bell309
measure bell309
cnot bell309 bell308
cnot bell308 c7
cnot bell306 c7
H bell306
measure bell306
cz bell306 b1
T* c7
H bell310
cnot bell310 bell311
cnot b2 bell311
measure bell311
cnot bell311 bell310
cnot bell310 c7
T c7
cnot bell308 c7
H bell308
measure bell308
cz bell308 a5
T* c7
H bell312
cnot bell312 bell313
cnot a4 bell313
measure bell313
cnot bell313 bell312
cnot bell312 c7
cnot bell310 c7
H bell310
measure bell310
cz bell310 b2
T* c7
H bell314
cnot bell314 bell315
cnot b3 bell315
measure bell315
cnot bell315 bell314
cnot bell314 c7
T c7
cnot bell312 c7
H bell312
measure bell312
cz bell312 a4
T* c7
H bell316
cnot bell316 bell317
cnot a3 bell317
measure bell317
cnot bell317 bell316
cnot bell316 c7
cnot bell314 c7
H bell314
measure bell314
cz bell314 b3
T* c7
H bell318
cnot bell318 bell319
cnot b4 bell319
measure bell319
cnot bell319 bell318
cnot bell318 c7
T c7
cnot bell316 c7
H bell316
measure bell316
cz bell316 a3
T* c7
H bell320
cnot bell320 bell321
cnot a2 bell321
measure bell321
cnot bell321 bell320
cnot bell320 c7
cnot bell318 c7
H bell318
measure bell318
cz bell318 b4
T* c7
H bell322
cnot bell322 bell323
cnot b5 bell323
measure bell323
cnot bell323 bell322
cnot bell322 c7
T c7
cnot bell320 c7
H bell320
measure bell320
cz bell320 a2
T* c7
H bell324
cnot bell324 bell325
cnot a1 bell325
measure bell325
cnot bell325 bell324
cnot bell324 c7
cnot bell322 c7
H bell322
measure bell322
cz bell322 b5
T* c7
H bell326
cnot bell326 bell327
cnot b6 bell327
measure bell327
cnot bell327 bell326
cnot bell326 c7
T c7
cnot bell324 c7
H bell324
measure bell324
cz bell324 a1
T* c7
H bell328
cnot bell328 bell329
cnot a0 bell329
measure bell329
cnot bell329 bell328
cnot bell328 c7
cnot bell326 c7
H bell326
measure bell326
cz bell326 b6
T* c7
H bell330
cnot bell330 bell331
cnot b7 bell331
measure bell331
cnot bell331 bell330
cnot bell330 c7
T c7
cnot bell328 c7
H bell328
measure bell328
cz bell328 a0
T* c7
cnot bell330 c7
H bell330
measure bell330
cz bell330 b7
H c7
T c8
H bell332
cnot bell332 bell333
cnot a8 bell333
measure bell333
cnot bell333 bell332
cnot bell332 c8
T* c8
H bell334
cnot bell334 bell335
cnot b0 bell335
measure bell335
cnot bell335 bell334
cnot bell334 c8
T c8
cnot bell332 c8
H bell332
measure bell332
cz bell332 a8
T* c8
H bell336
cnot bell336 bell337
cnot a7 bell337
measure bell337
cnot bell337 bell336
cnot bell336 c8
cnot bell334 c8
H bell334
measure bell334
cz bell334 b0
T* c8
H bell338
cnot bell338 bell339
cnot b1 bell339
measure bell339
cnot bell339 bell338
cnot bell338 c8
T c8
cnot bell336 c8
H bell336
measure bell336
cz bell336 a7
T* c8
H bell340
cnot bell340 bell341
cnot a6 bell341
measure bell341
cnot bell341 bell340
cnot bell340 c8
cnot bell338 c8
H bell338
measure bell338
cz bell338 b1
T* c8
H bell342
cnot bell342 bell343
cnot b2 bell343
measure bell343
cnot bell343 bell342
cnot bell342 c8
T c8
cnot bell340 c8
H bell340
measure bell340
cz bell340 a6
T* c8
H bell344
cnot bell344 bell345
cnot a5 bell345
measure bell345
cnot bell345 bell344
cnot bell344 c8
cnot bell342 c8
H bell342
measure bell342
cz bell342 b2
T* c8
H bell346
cnot bell346 bell347
cnot b3 bell347
measure bell347
cnot bell347 bell346
cnot bell346 c8
T c8
cnot bell344 c8
H bell344
measure bell344
cz bell344 a5
T* c8
H bell348
cnot bell348 bell349
cnot a4 bell349
measure bell349
cnot bell349 bell348
cnot bell348 c8
cnot bell346 c8
H bell346
measure bell346
cz bell346 b3
T* c8
H bell350
cnot bell350 bell351
cnot b4 bell351
measure bell351
cnot bell351 bell350
cnot bell350 c8
T c8
cnot bell348 c8
H bell348
measure bell348
cz bell348 a4
T* c8
H bell352
cnot bell352 bell353
cnot a3 bell353
measure bell353
cnot bell353 bell352
cnot bell352 c8
cnot bell350 c8
H bell350
measure bell350
cz bell350 b4
T* c8
H bell354
cnot bell354 bell355
cnot b5 bell355
measure bell355
cnot bell355 bell354
cnot bell354 c8
T c8
cnot bell352 c8
H bell352
measure bell352
cz bell352 a3
T* c8
H bell356
cnot bell356 bell357
cnot a2 bell357
measure bell357
cnot bell357 bell356
cnot bell356 c8
cnot bell354 c8
H bell354
measure bell354
cz bell354 b5
T* c8
H bell358
cnot bell358 bell359
cnot b6 bell359
measure bell359
cnot bell359 bell358
cnot bell358 c8
T c8
cnot bell356 c8
H bell356
measure bell356
cz bell356 a2
T* c8
H bell360
cnot bell360 bell361
cnot a1 bell361
measure bell361
cnot bell361 bell360
cnot bell360 c8
cnot bell358 c8
H bell358
measure bell358
cz bell358 b6
T* c8
H bell362
cnot bell362 bell363
cnot b7 bell363
measure bell363
cnot bell363 bell362
cnot bell362 c8
T c8
cnot bell360 c8
H bell360
measure bell360
cz bell360 a1
T* c8
H bell364
cnot bell364 bell365
cnot a0 bell365
measure bell365
cnot bell365 bell364
cnot bell364 c8
cnot bell362 c8
H bell362
measure bell362
cz bell362 b7
T* c8
H bell366
cnot bell366 bell367
cnot b8 bell367
measure bell367
cnot bell367 bell366
cnot bell366 c8
T c8
cnot bell364 c8
H bell364
measure bell364
cz bell364 a0
T* c8
cnot bell366 c8
H bell366
measure bell366
cz bell366 b8
H c8
S c9
H bell368
cnot bell368 bell369
cnot a9 bell369
measure bell369
cnot bell369 bell368
cnot bell368 c9
T* c9
H bell370
cnot bell370 bell371
cnot b0 bell371
measure bell371
cnot bell371 bell370
cnot bell370 c9
T c9
cnot bell368 c9
H bell368
measure bell368
cz bell368 a9
T* c9
H bell372
cnot bell372 bell373
cnot a8 bell373
measure bell373
cnot bell373 bell372
cnot bell372 c9
cnot bell370 c9
H bell370
measure bell370
cz bell370 b0
T* c9
H bell374
cnot bell374 bell375
cnot b1 bell375
measure bell375
cnot bell375 bell374
cnot bell374 c9
T c9
cnot bell372 c9
H bell372
measure bell372
cz bell372 a8
T* c9
H bell376
cnot bell376 bell377
cnot a7 bell377
measure bell377
cnot bell377 bell376
cnot bell376 c9
cnot bell374 c9
H bell374
measure bell374
cz bell374 b1
T* c9
H bell378
cnot bell378 bell379
cnot b2 bell379
measure bell379
cnot bell379 bell378
cnot bell378 c9
T c9
cnot bell376 c9
H bell376
measure bell376
cz bell376 a7
T* c9
H bell380
cnot bell380 bell381
cnot a6 bell381
measure bell381
cnot bell381 bell380
cnot bell380 c9
cnot bell378 c9
H bell378
measure bell378
cz bell378 b2
T* c9
H bell382
cnot bell382 bell383
cnot b3 bell383
measure bell383
cnot bell383 bell382
cnot bell382 c9
T c9
cnot bell380 c9
H bell380
measure bell380
cz bell380 a6
T* c9
H bell384
cnot bell384 bell385
cnot a5 bell385
measure bell385
cnot bell385 bell384
cnot bell384 c9
cnot bell382 c9
H bell382
measure bell382
cz bell382 b3
T* c9
H bell386
cnot bell386 bell387
cnot b4 bell387
measure bell387
cnot bell387 bell386
cnot bell386 c9
T c9
cnot bell384 c9
H bell384
measure bell384
cz bell384 a5
T* c9
H bell388
cnot bell388 bell389
cnot a4 bell389
measure bell389
cnot bell389 bell388
cnot bell388 c9
cnot bell386 c9
H bell386
measure bell386
cz bell386 b4
T* c9
H bell390
cnot bell390 bell391
cnot b5 bell391
measure bell391
cnot bell391 bell390
cnot bell390 c9
T c9
cnot bell388 c9
H bell388
measure bell388
cz bell388 a4
T* c9
H bell392
cnot bell392 bell393
cnot a3 bell393
measure bell393
cnot bell393 bell392
cnot bell392 c9
cnot bell390 c9
H bell390
measure bell390
cz bell390 b5
T* c9
H bell394
cnot bell394 bell395
cnot b6 bell395
measure bell395
cnot bell395 bell394
cnot bell394 c9
T c9
cnot bell392 c9
H bell392
measure bell392
cz bell392 a3
T* c9
H bell396
cnot bell396 bell397
cnot a2 bell397
measure bell397
cnot bell397 bell396
cnot bell396 c9
cnot bell394 c9
H bell394
measure bell394
cz bell394 b6
T* c9
H bell398
cnot bell398 bell399
cnot b7 bell399
measure bell399
cnot bell399 bell398
cnot bell398 c9
T c9
cnot bell396 c9
H bell396
measure bell396
cz bell396 a2
T* c9
H bell400
cnot bell400 bell401
cnot a1 bell401
measure bell401
cnot bell401 bell400
cnot bell400 c9
cnot bell398 c9
H bell398
measure bell398
cz bell398 b7
T* c9
H bell402
cnot bell402 bell403
cnot b8 bell403
measure bell403
cnot bell403 bell402
cnot bell402 c9
T c9
cnot bell400 c9
H bell400
measure bell400
cz bell400 a1
T* c9
H bell404
cnot bell404 bell405
cnot a0 bell405
measure bell405
cnot bell405 bell404
cnot bell404 c9
cnot bell402 c9
H bell402
measure bell402
cz bell402 b8
T* c9
H bell406
cnot bell406 bell407
cnot b9 bell407
measure bell407
cnot bell407 bell406
cnot bell406 c9
T c9
cnot bell404 c9
H bell404
measure bell404
cz bell404 a0
T* c9
cnot bell406 c9
H bell406
measure bell406
cz bell406 b9
H c9
S a0
S a1
S b0
H bell408
cnot bell408 bell409
cnot a0 bell409
measure bell409
cnot bell409 bell408
cnot bell408 b0
T* b0
cnot a1 b0
cnot bell408 b0
H bell408
measure bell408
cz bell408 a0
T* b0
S b1
H bell410
cnot bell410 bell411
cnot a0 bell411
measure bell411
cnot bell411 bell410
cnot bell410 b1
T* b1
H bell412
cnot bell412 bell413
cnot a1 bell413
measure bell413
cnot bell413 bell412
cnot bell412 b1
H bell412
measure bell412
cz bell412 a1
cnot bell410 b1
T* b1
S a2
H bell414
cnot bell414 bell415
cnot b0 bell415
measure bell415
cnot bell415 bell414
cnot bell414 a2
H bell416
cnot bell416 bell417
cnot a1 bell417
measure bell417
cnot bell417 bell416
cnot bell416 a2
H bell416
measure bell416
cz bell416 a1
T* a2
H bell418
cnot bell418 bell419
cnot b1 bell419
measure bell419
cnot bell419 bell418
cnot bell418 a2
H bell418
measure bell418
cz bell418 b1
cnot bell414 a2
H bell414
measure bell414
cz bell414 b0
T* a2
S b2
cnot bell410 b2
T* b2
H bell420
cnot bell420 bell421
cnot a1 bell421
measure bell421
cnot bell421 bell420
cnot bell420 b2
H bell420
measure bell420
cz bell420 a1
cnot bell410 b2
H bell410
measure bell410
cz bell410 a0
T* b2
cnot b1 b2
H bell422
cnot bell422 bell423
cnot a2 bell423
measure bell423
cnot bell423 bell422
cnot bell422 b2
H bell422
measure bell422
cz bell422 a2
T* b2
S a3
H bell424
cnot bell424 bell425
cnot b0 bell425
measure bell425
cnot bell425 bell424
cnot bell424 a3
H bell426
cnot bell426 bell427
cnot a1 bell427
measure bell427
cnot bell427 bell426
cnot bell426 a3
T* a3
H bell428
cnot bell428 bell429
cnot b1 bell429
measure bell429
cnot bell429 bell428
cnot bell428 a3
cnot bell424 a3
H bell424
measure bell424
cz bell424 b0
T* a3
H bell430
cnot bell430 bell431
cnot b2 bell431
measure bell431
cnot bell431 bell430
cnot bell430 a3
H bell432
cnot bell432 bell433
cnot a2 bell433
measure bell433
cnot bell433 bell432
cnot bell432 a3
T* a3
S b3
H bell434
cnot bell434 bell435
cnot a0 bell435
measure bell435
cnot bell435 bell434
cnot bell434 b3
T* b3
cnot bell426 b3
H bell426
measure bell426
cz bell426 a1
cnot bell434 b3
H bell434
measure bell434
cz bell434 a0
T* b3
cnot bell428 b3
H bell428
measure bell428
cz bell428 b1
cnot bell432 b3
H bell432
measure bell432
cz bell432 a2
T* b3
cnot bell430 b3
H bell430
measure bell430
cz bell430 b2
cnot a3 b3
T* b3
S a4
H bell436
cnot bell436 bell437
cnot b0 bell437
measure bell437
cnot bell437 bell436
cnot bell436 a4
H bell438
cnot bell438 bell439
cnot a1 bell439
measure bell439
cnot bell439 bell438
cnot bell438 a4
H bell438
measure bell438
cz bell438 a1
T* a4
H bell440
cnot bell440 bell441
cnot b1 bell441
measure bell441
cnot bell441 bell440
cnot bell440 a4
H bell440
measure bell440
cz bell440 b1
cnot bell436 a4
T* a4
H bell442
cnot bell442 bell443
cnot b2 bell443
measure bell443
cnot bell443 bell442
cnot bell442 a4
H bell442
measure bell442
cz bell442 b2
H bell444
cnot bell444 bell445
cnot a2 bell445
measure bell445
cnot bell445 bell444
cnot bell444 a4
H bell444
measure bell444
cz bell444 a2
T* a4
H bell446
cnot bell446 bell447
cnot b3 bell447
measure bell447
cnot bell447 bell446
cnot bell446 a4
H bell446
measure bell446
cz bell446 b3
H bell448
cnot bell448 bell449
cnot a3 bell449
measure bell449
cnot bell449 bell448
cnot bell448 a4
H bell448
measure bell448
cz bell448 a3
T* a4
S b4
H bell450
cnot bell450 bell451
cnot a0 bell451
measure bell451
cnot bell451 bell450
cnot bell450 b4
T* b4
H bell452
cnot bell452 bell453
cnot a1 bell453
measure bell453
cnot bell453 bell452
cnot bell452 b4
H bell452
measure bell452
cz bell452 a1
cnot bell450 b4
H bell450
measure bell450
cz bell450 a0
T* b4
H bell454
cnot bell454 bell455
cnot b1 bell455
measure bell455
cnot bell455 bell454
cnot bell454 b4
H bell454
measure bell454
cz bell454 b1
H bell456
cnot bell456 bell457
cnot a2 bell457
measure bell457
cnot bell457 bell456
cnot bell456 b4
H bell456
measure bell456
cz bell456 a2
T* b4
H bell458
cnot bell458 bell459
cnot b2 bell459
measure bell459
cnot bell459 bell458
cnot bell458 b4
H bell458
measure bell458
cz bell458 b2
H bell460
cnot bell460 bell461
cnot a3 bell461
measure bell461
cnot bell461 bell460
cnot bell460 b4
H bell460
measure bell460
cz bell460 a3
T* b4
H bell462
cnot bell462 bell463
cnot b3 bell463
measure bell463
cnot bell463 bell462
cnot bell462 b4
H bell462
measure bell462
cz bell462 b3
H bell464
cnot bell464 bell465
cnot a4 bell465
measure bell465
cnot bell465 bell464
cnot bell464 b4
H bell464
measure bell464
cz bell464 a4
T* b4
S a5
cnot bell436 a5
H bell466
cnot bell466 bell467
cnot a1 bell467
measure bell467
cnot bell467 bell466
cnot bell466 a5
H bell466
measure bell466
cz bell466 a1
T* a5
H bell468
cnot bell468 bell469
cnot b1 bell469
measure bell469
cnot bell469 bell468
cnot bell468 a5
H bell468
measure bell468
cz bell468 b1
cnot bell436 a5
H bell436
measure bell436
cz bell436 b0
T* a5
H bell470
cnot bell470 bell471
cnot b2 bell471
measure bell471
cnot bell471 bell470
cnot bell470 a5
H bell470
measure bell470
cz bell470 b2
H bell472
cnot bell472 bell473
cnot a2 bell473
measure bell473
cnot bell473 bell472
cnot bell472 a5
H bell472
measure bell472
cz bell472 a2
T* a5
H bell474
cnot bell474 bell475
cnot b3 bell475
measure bell475
cnot bell475 bell474
cnot bell474 a5
H bell474
measure bell474
cz bell474 b3
H bell476
cnot bell476 bell477
cnot a3 bell477
measure bell477
cnot bell477 bell476
cnot bell476 a5
H bell476
measure bell476
cz bell476 a3
T* a5
H bell478
cnot bell478 bell479
cnot b4 bell479
measure bell479
cnot bell479 bell478
cnot bell478 a5
H bell478
measure bell478
cz bell478 b4
cnot a4 a5
T* a5
S b5
H bell480
cnot bell480 bell481
cnot a0 bell481
measure bell481
cnot bell481 bell480
cnot bell480 b5
T* b5
H bell482
cnot bell482 bell483
cnot a1 bell483
measure bell483
cnot bell483 bell482
cnot bell482 b5
H bell482
measure bell482
cz bell482 a1
cnot bell480 b5
H bell480
measure bell480
cz bell480 a0
T* b5
H bell484
cnot bell484 bell485
cnot b1 bell485
measure bell485
cnot bell485 bell484
cnot bell484 b5
H bell484
measure bell484
cz bell484 b1
H bell486
cnot bell486 bell487
cnot a2 bell487
measure bell487
cnot bell487 bell486
cnot bell486 b5
H bell486
measure bell486
cz bell486 a2
T* b5
H bell488
cnot bell488 bell489
cnot b2 bell489
measure bell489
cnot bell489 bell488
cnot bell488 b5
H bell488
measure bell488
cz bell488 b2
H bell490
cnot bell490 bell491
cnot a3 bell491
measure bell491
cnot bell491 bell490
cnot bell490 b5
H bell490
measure bell490
cz bell490 a3
T* b5
H bell492
cnot bell492 bell493
cnot b3 bell493
measure bell493
cnot bell493 bell492
cnot bell492 b5
H bell492
measure bell492
cz bell492 b3
H bell494
cnot bell494 bell495
cnot a4 bell495
measure bell495
cnot bell495 bell494
cnot bell494 b5
H bell494
measure bell494
cz bell494 a4
T* b5
H bell496
cnot bell496 bell497
cnot b4 bell497
measure bell497
cnot bell497 bell496
cnot bell496 b5
H bell496
measure bell496
cz bell496 b4
H bell498
cnot bell498 bell499
cnot a5 bell499
measure bell499
cnot bell499 bell498
cnot bell498 b5
H bell498
measure bell498
cz bell498 a5
T* b5
S a6
H bell500
cnot bell500 bell501
cnot b0 bell501
measure bell501
cnot bell501 bell500
cnot bell500 a6
H bell502
cnot bell502 bell503
cnot a1 bell503
measure bell503
cnot bell503 bell502
cnot bell502 a6
H bell502
measure bell502
cz bell502 a1
T* a6
H bell504
cnot bell504 bell505
cnot b1 bell505
measure bell505
cnot bell505 bell504
cnot bell504 a6
H bell504
measure bell504
cz bell504 b1
cnot bell500 a6
H bell500
measure bell500
cz bell500 b0
T* a6
H bell506
cnot bell506 bell507
cnot b2 bell507
measure bell507
cnot bell507 bell506
cnot bell506 a6
H bell506
measure bell506
cz bell506 b2
H bell508
cnot bell508 bell509
cnot a2 bell509
measure bell509
cnot bell509 bell508
cnot bell508 a6
H bell508
measure bell508
cz bell508 a2
T* a6
H bell510
cnot bell510 bell511
cnot b3 bell511
measure bell511
cnot bell511 bell510
cnot bell510 a6
H bell510
measure bell510
cz bell510 b3
H bell512
cnot bell512 bell513
cnot a3 bell513
measure bell513
cnot bell513 bell512
cnot bell512 a6
H bell512
measure bell512
cz bell512 a3
T* a6
H bell514
cnot bell514 bell515
cnot b4 bell515
measure bell515
cnot bell515 bell514
cnot bell514 a6
H bell514
measure bell514
cz bell514 b4
H bell516
cnot bell516 bell517
cnot a4 bell517
measure bell517
cnot bell517 bell516
cnot bell516 a6
H bell516
measure bell516
cz bell516 a4
T* a6
H bell518
cnot bell518 bell519
cnot b5 bell519
measure bell519
cnot bell519 bell518
cnot bell518 a6
H bell518
measure bell518
cz bell518 b5
H bell520
cnot bell520 bell521
cnot a5 bell521
measure bell521
cnot bell521 bell520
cnot bell520 a6
H bell520
measure bell520
cz bell520 a5
T* a6
S b6
H bell522
cnot bell522 bell523
cnot a0 bell523
measure bell523
cnot bell523 bell522
cnot bell522 b6
T* b6
H bell524
cnot bell524 bell525
cnot a1 bell525
measure bell525
cnot bell525 bell524
cnot bell524 b6
H bell524
measure bell524
cz bell524 a1
cnot bell522 b6
H bell522
measure bell522
cz bell522 a0
T* b6
H bell526
cnot bell526 bell527
cnot b1 bell527
measure bell527
cnot bell527 bell526
cnot bell526 b6
H bell526
measure bell526
cz bell526 b1
H bell528
cnot bell528 bell529
cnot a2 bell529
measure bell529
cnot bell529 bell528
cnot bell528 b6
H bell528
measure bell528
cz bell528 a2
T* b6
H bell530
cnot bell530 bell531
cnot b2 bell531
measure bell531
cnot bell531 bell530
cnot bell530 b6
H bell530
measure bell530
cz bell530 b2
H bell532
cnot bell532 bell533
cnot a3 bell533
measure bell533
cnot bell533 bell532
cnot bell532 b6
H bell532
measure bell532
cz bell532 a3
T* b6
H bell534
cnot bell534 bell535
cnot b3 bell535
measure bell535
cnot bell535 bell534
cnot bell534 b6
H bell534
measure bell534
cz bell534 b3
H bell536
cnot bell536 bell537
cnot a4 bell537
measure bell537
cnot bell537 bell536
cnot bell536 b6
H bell536
measure bell536
cz bell536 a4
T* b6
cnot b4 b6
H bell538
cnot bell538 bell539
cnot a5 bell539
measure bell539
cnot bell539 bell538
cnot bell538 b6
H bell538
measure bell538
cz bell538 a5
T* b6
H bell540
cnot bell540 bell541
cnot b5 bell541
measure bell541
cnot bell541 bell540
cnot bell540 b6
H bell540
measure bell540
cz bell540 b5
H bell542
cnot bell542 bell543
cnot a6 bell543
measure bell543
cnot bell543 bell542
cnot bell542 b6
H bell542
measure bell542
cz bell542 a6
T* b6
S a7
H bell544
cnot bell544 bell545
cnot b0 bell545
measure bell545
cnot bell545 bell544
cnot bell544 a7
H bell546
cnot bell546 bell547
cnot a1 bell547
measure bell547
cnot bell547 bell546
cnot bell546 a7
T* a7
H bell548
cnot bell548 bell549
cnot b1 bell549
measure bell549
cnot bell549 bell548
cnot bell548 a7
cnot bell544 a7
H bell544
measure bell544
cz bell544 b0
T* a7
H bell550
cnot bell550 bell551
cnot b2 bell551
measure bell551
cnot bell551 bell550
cnot bell550 a7
H bell552
cnot bell552 bell553
cnot a2 bell553
measure bell553
cnot bell553 bell552
cnot bell552 a7
T* a7
H bell554
cnot bell554 bell555
cnot b3 bell555
measure bell555
cnot bell555 bell554
cnot bell554 a7
H bell556
cnot bell556 bell557
cnot a3 bell557
measure bell557
cnot bell557 bell556
cnot bell556 a7
T* a7
H bell558
cnot bell558 bell559
cnot b4 bell559
measure bell559
cnot bell559 bell558
cnot bell558 a7
H bell560
cnot bell560 bell561
cnot a4 bell561
measure bell561
cnot bell561 bell560
cnot bell560 a7
T* a7
H bell562
cnot bell562 bell563
cnot b5 bell563
measure bell563
cnot bell563 bell562
cnot bell562 a7
H bell564
cnot bell564 bell565
cnot a5 bell565
measure bell565
cnot bell565 bell564
cnot bell564 a7
T* a7
H bell566
cnot bell566 bell567
cnot b6 bell567
measure bell567
cnot bell567 bell566
cnot bell566 a7
H bell568
cnot bell568 bell569
cnot a6 bell569
measure bell569
cnot bell569 bell568
cnot bell568 a7
T* a7
S b7
H bell570
cnot bell570 bell571
cnot a0 bell571
measure bell571
cnot bell571 bell570
cnot bell570 b7
T* b7
cnot bell546 b7
H bell546
measure bell546
cz bell546 a1
cnot bell570 b7
H bell570
measure bell570
cz bell570 a0
T* b7
cnot bell548 b7
H bell548
measure bell548
cz bell548 b1
cnot bell552 b7
H bell552
measure bell552
cz bell552 a2
T* b7
cnot bell550 b7
H bell550
measure bell550
cz bell550 b2
cnot bell556 b7
H bell556
measure bell556
cz bell556 a3
T* b7
cnot bell554 b7
H bell554
measure bell554
cz bell554 b3
cnot bell560 b7
H bell560
measure bell560
cz bell560 a4
T* b7
cnot bell558 b7
H bell558
measure bell558
cz bell558 b4
cnot bell564 b7
H bell564
measure bell564
cz bell564 a5
T* b7
cnot bell562 b7
H bell562
measure bell562
cz bell562 b5
cnot bell568 b7
H bell568
measure bell568
cz bell568 a6
T* b7
cnot bell566 b7
H bell566
measure bell566
cz bell566 b6
cnot a7 b7
T* b7
S a8
H bell572
cnot bell572 bell573
cnot b0 bell573
measure bell573
cnot bell573 bell572
cnot bell572 a8
H bell574
cnot bell574 bell575
cnot a1 bell575
measure bell575
cnot bell575 bell574
cnot bell574 a8
H bell574
measure bell574
cz bell574 a1
T* a8
H bell576
cnot bell576 bell577
cnot b1 bell577
measure bell577
cnot bell577 bell576
cnot bell576 a8
H bell576
measure bell576
cz bell576 b1
cnot bell572 a8
H bell572
measure bell572
cz bell572 b0
T* a8
H bell578
cnot bell578 bell579
cnot b2 bell579
measure bell579
cnot bell579 bell578
cnot bell578 a8
H bell578
measure bell578
cz bell578 b2
H bell580
cnot bell580 bell581
cnot a2 bell581
measure bell581
cnot bell581 bell580
cnot bell580 a8
H bell580
measure bell580
cz bell580 a2
T* a8
H bell582
cnot bell582 bell583
cnot b3 bell583
measure bell583
cnot bell583 bell582
cnot bell582 a8
H bell582
measure bell582
cz bell582 b3
H bell584
cnot bell584 bell585
cnot a3 bell585
measure bell585
cnot bell585 bell584
cnot bell584 a8
H bell584
measure bell584
cz bell584 a3
T* a8
H bell586
cnot bell586 bell587
cnot b4 bell587
measure bell587
cnot bell587 bell586
cnot bell586 a8
H bell586
measure bell586
cz bell586 b4
H bell588
cnot bell588 bell589
cnot a4 bell589
measure bell589
cnot bell589 bell588
cnot bell588 a8
H bell588
measure bell588
cz bell588 a4
T* a8
H bell590
cnot bell590 bell591
cnot b5 bell591
measure bell591
cnot bell591 bell590
cnot bell590 a8
H bell590
measure bell590
cz bell590 b5
H bell592
cnot bell592 bell593
cnot a5 bell593
measure bell593
cnot bell593 bell592
cnot bell592 a8
H bell592
measure bell592
cz bell592 a5
T* a8
H bell594
cnot bell594 bell595
cnot b6 bell595
measure bell595
cnot bell595 bell594
cnot bell594 a8
H bell594
measure bell594
cz bell594 b6
cnot a6 a8
T* a8
H bell596
cnot bell596 bell597
cnot b7 bell597
measure bell597
cnot bell597 bell596
cnot bell596 a8
H bell596
measure bell596
cz bell596 b7
H bell598
cnot bell598 bell599
cnot a7 bell599
measure bell599
cnot bell599 bell598
cnot bell598 a8
H bell598
measure bell598
cz bell598 a7
T* a8
S b8
H bell600
cnot bell600 bell601
cnot a0 bell601
measure bell601
cnot bell601 bell600
cnot bell600 b8
T* b8
H bell602
cnot bell602 bell603
cnot a1 bell603
measure bell603
cnot bell603 bell602
cnot bell602 b8
H bell602
measure bell602
cz bell602 a1
cnot bell600 b8
H bell600
measure bell600
cz bell600 a0
T* b8
H bell604
cnot bell604 bell605
cnot b1 bell605
measure bell605
cnot bell605 bell604
cnot bell604 b8
H bell604
measure bell604
cz bell604 b1
H bell606
cnot bell606 bell607
cnot a2 bell607
measure bell607
cnot bell607 bell606
cnot bell606 b8
H bell606
measure bell606
cz bell606 a2
T* b8
H bell608
cnot bell608 bell609
cnot b2 bell609
measure bell609
cnot bell609 bell608
cnot bell608 b8
H bell608
measure bell608
cz bell608 b2
H bell610
cnot bell610 bell611
cnot a3 bell611
measure bell611
cnot bell611 bell610
cnot bell610 b8
H bell610
measure bell610
cz bell610 a3
T* b8
H bell612
cnot bell612 bell613
cnot b3 bell613
measure bell613
cnot bell613 bell612
cnot bell612 b8
H bell612
measure bell612
cz bell612 b3
H bell614
cnot bell614 bell615
cnot a4 bell615
measure bell615
cnot bell615 bell614
cnot bell614 b8
H bell614
measure bell614
cz bell614 a4
T* b8
H bell616
cnot bell616 bell617
cnot b4 bell617
measure bell617
cnot bell617 bell616
cnot bell616 b8
H bell616
measure bell616
cz bell616 b4
H bell618
cnot bell618 bell619
cnot a5 bell619
measure bell619
cnot bell619 bell618
cnot bell618 b8
H bell618
measure bell618
cz bell618 a5
T* b8
cnot b5 b8
H bell620
cnot bell620 bell621
cnot a6 bell621
measure bell621
cnot bell621 bell620
cnot bell620 b8
H bell620
measure bell620
cz bell620 a6
T* b8
H bell622
cnot bell622 bell623
cnot b8 bell623
measure bell623
cnot bell623 bell622
H bell624
cnot bell624 bell625
cnot b6 bell625
measure bell625
cnot bell625 bell624
cnot bell624 bell622
H bell626
cnot bell626 bell627
cnot a7 bell627
measure bell627
cnot bell627 bell626
cnot bell626 bell622
H bell628
cnot bell628 bell629
cnot bell622 bell629
measure bell629
cnot bell629 bell628
reset bell629
cnot b8 bell628
cnot bell628 b8
H bell628
measure bell628
cz bell628 a7
cz bell628 b6
H bell622
measure bell622
cz bell622 b8
T* b8
H bell630
cnot bell630 bell631
cnot b8 bell631
measure bell631
cnot bell631 bell630
H bell632
cnot bell632 bell633
cnot b7 bell633
measure bell633
cnot bell633 bell632
cnot bell632 bell630
H bell634
cnot bell634 bell635
cnot a8 bell635
measure bell635
cnot bell635 bell634
cnot bell634 bell630
H bell636
cnot bell636 bell637
cnot bell630 bell637
measure bell637
cnot bell637 bell636
reset bell637
cnot b8 bell636
cnot bell636 b8
H bell636
measure bell636
cz bell636 a8
cz bell636 b7
H bell630
measure bell630
cz bell630 b8
T* b8
S a9
H bell638
cnot bell638 bell639
cnot b0 bell639
measure bell639
cnot bell639 bell638
cnot bell638 a9
H bell640
cnot bell640 bell641
cnot a1 bell641
measure bell641
cnot bell641 bell640
cnot bell640 a9
T* a9
H bell642
cnot bell642 bell643
cnot b1 bell643
measure bell643
cnot bell643 bell642
cnot bell642 a9
cnot bell638 a9
H bell638
measure bell638
cz bell638 b0
T* a9
H bell644
cnot bell644 bell645
cnot b2 bell645
measure bell645
cnot bell645 bell644
cnot bell644 a9
H bell646
cnot bell646 bell647
cnot a2 bell647
measure bell647
cnot bell647 bell646
cnot bell646 a9
T* a9
H bell648
cnot bell648 bell649
cnot b3 bell649
measure bell649
cnot bell649 bell648
cnot bell648 a9
H bell650
cnot bell650 bell651
cnot a3 bell651
measure bell651
cnot bell651 bell650
cnot bell650 a9
T* a9
H bell652
cnot bell652 bell653
cnot b4 bell653
measure bell653
cnot bell653 bell652
cnot bell652 a9
H bell654
cnot bell654 bell655
cnot a4 bell655
measure bell655
cnot bell655 bell654
cnot bell654 a9
T* a9
H bell656
cnot bell656 bell657
cnot b5 bell657
measure bell657
cnot bell657 bell656
cnot bell656 a9
H bell658
cnot bell658 bell659
cnot a5 bell659
measure bell659
cnot bell659 bell658
cnot bell658 a9
T* a9
cnot bell624 a9
H bell660
cnot bell660 bell661
cnot a6 bell661
measure bell661
cnot bell661 bell660
cnot bell660 a9
T* a9
cnot bell632 a9
cnot bell626 a9
T* a9
H bell662
cnot bell662 bell663
cnot b8 bell663
measure bell663
cnot bell663 bell662
cnot bell662 a9
cnot bell634 a9
T* a9
S b9
H bell664
cnot bell664 bell665
cnot a0 bell665
measure bell665
cnot bell665 bell664
cnot bell664 b9
T* b9
cnot bell640 b9
H bell640
measure bell640
cz bell640 a1
cnot bell664 b9
H bell664
measure bell664
cz bell664 a0
T* b9
cnot bell642 b9
H bell642
measure bell642
cz bell642 b1
cnot bell646 b9
H bell646
measure bell646
cz bell646 a2
T* b9
cnot bell644 b9
H bell644
measure bell644
cz bell644 b2
cnot bell650 b9
H bell650
measure bell650
cz bell650 a3
T* b9
cnot bell648 b9
H bell648
measure bell648
cz bell648 b3
cnot bell654 b9
H bell654
measure bell654
cz bell654 a4
T* b9
cnot bell652 b9
H bell652
measure bell652
cz bell652 b4
cnot bell658 b9
H bell658
measure bell658
cz bell658 a5
T* b9
cnot bell656 b9
H bell656
measure bell656
cz bell656 b5
cnot bell660 b9
H bell660
measure bell660
cz bell660 a6
T* b9
cnot bell624 b9
H bell624
measure bell624
cz bell624 b6
cnot bell626 b9
H bell626
measure bell626
cz bell626 a7
T* b9
cnot bell632 b9
H bell632
measure bell632
cz bell632 b7
cnot bell634 b9
H bell634
measure bell634
cz bell634 a8
T* b9
cnot bell662 b9
cnot a9 b9
T* b9
H bell666
cnot bell666 bell667
cnot b1 bell667
measure bell667
cnot bell667 bell666
cnot bell666 a2
H bell666
measure bell666
cz bell666 b1
H bell668
cnot bell668 bell669
cnot b2 bell669
measure bell669
cnot bell669 bell668
cnot bell668 a3
H bell668
measure bell668
cz bell668 b2
H bell670
cnot bell670 bell671
cnot b3 bell671
measure bell671
cnot bell671 bell670
cnot bell670 a4
H bell670
measure bell670
cz bell670 b3
H bell672
cnot bell672 bell673
cnot b4 bell673
measure bell673
cnot bell673 bell672
cnot bell672 a5
H bell672
measure bell672
cz bell672 b4
H bell674
cnot bell674 bell675
cnot b5 bell675
measure bell675
cnot bell675 bell674
cnot bell674 a6
H bell674
measure bell674
cz bell674 b5
H bell676
cnot bell676 bell677
cnot b6 bell677
measure bell677
cnot bell677 bell676
cnot bell676 a7
H bell676
measure bell676
cz bell676 b6
H bell678
cnot bell678 bell679
cnot b7 bell679
measure bell679
cnot bell679 bell678
cnot bell678 a8
H bell678
measure bell678
cz bell678 b7
cnot bell662 a9
H bell662
measure bell662
cz bell662 b8
cnot a9 b9
H bell680
cnot bell680 bell681
cnot a7 bell681
measure bell681
cnot bell681 bell680
cnot bell680 a8
H bell680
measure bell680
cz bell680 a7
cnot a6 a8
H bell682
cnot bell682 bell683
cnot a6 bell683
measure bell683
cnot bell683 bell682
cnot bell682 a7
H bell682
measure bell682
cz bell682 a6
H bell684
cnot bell684 bell685
cnot a8 bell685
measure bell685
cnot bell685 bell684
cnot bell684 b9
H bell684
measure bell684
cz bell684 a8
H bell686
cnot bell686 bell687
cnot a8 bell687
measure bell687
cnot bell687 bell686
cnot bell686 b8
H bell686
measure bell686
cz bell686 a8
cnot a7 b7
H bell688
cnot bell688 bell689
cnot a6 bell689
measure bell689
cnot bell689 bell688
cnot bell688 b6
H bell688
measure bell688
cz bell688 a6
H bell690
cnot bell690 bell691
cnot a8 bell691
measure bell691
cnot bell691 bell690
cnot bell690 a9
H bell690
measure bell690
cz bell690 a8
cnot a4 a5
H bell692
cnot bell692 bell693
cnot a3 bell693
measure bell693
cnot bell693 bell692
cnot bell692 a5
cnot bell692 a4
H bell692
measure bell692
cz bell692 a3
H bell694
cnot bell694 bell695
cnot a5 bell695
measure bell695
cnot bell695 bell694
cnot bell694 b9
H bell694
measure bell694
cz bell694 a5
H bell696
cnot bell696 bell697
cnot a5 bell697
measure bell697
cnot bell697 bell696
cnot bell696 b8
H bell696
measure bell696
cz bell696 a5
H bell698
cnot bell698 bell699
cnot a5 bell699
measure bell699
cnot bell699 bell698
cnot bell698 b7
H bell698
measure bell698
cz bell698 a5
H bell700
cnot bell700 bell701
cnot a5 bell701
measure bell701
cnot bell701 bell700
cnot bell700 b6
H bell700
measure bell700
cz bell700 a5
H bell702
cnot bell702 bell703
cnot a5 bell703
measure bell703
cnot bell703 bell702
cnot bell702 b5
H bell702
measure bell702
cz bell702 a5
H bell704
cnot bell704 bell705
cnot a4 bell705
measure bell705
cnot bell705 bell704
cnot bell704 b4
H bell704
measure bell704
cz bell704 a4
cnot a3 b3
H bell706
cnot bell706 bell707
cnot a5 bell707
measure bell707
cnot bell707 bell706
cnot bell706 a9
H bell706
measure bell706
cz bell706 a5
H bell708
cnot bell708 bell709
cnot a5 bell709
measure bell709
cnot bell709 bell708
cnot bell708 a8
H bell708
measure bell708
cz bell708 a5
H bell710
cnot bell710 bell711
cnot a5 bell711
measure bell711
cnot bell711 bell710
cnot bell710 a7
H bell710
measure bell710
cz bell710 a5
H bell712
cnot bell712 bell713
cnot a5 bell713
measure bell713
cnot bell713 bell712
cnot bell712 a6
H bell712
measure bell712
cz bell712 a5
H bell714
cnot bell714 bell715
cnot a1 bell715
measure bell715
cnot bell715 bell714
cnot bell714 a2
H bell714
measure bell714
cz bell714 a1
H bell716
cnot bell716 bell717
cnot a2 bell717
measure bell717
cnot bell717 bell716
cnot bell716 b9
H bell716
measure bell716
cz bell716 a2
H bell718
cnot bell718 bell719
cnot a2 bell719
measure bell719
cnot bell719 bell718
cnot bell718 b8
H bell718
measure bell718
cz bell718 a2
H bell720
cnot bell720 bell721
cnot a2 bell721
measure bell721
cnot bell721 bell720
cnot bell720 b7
H bell720
measure bell720
cz bell720 a2
H bell722
cnot bell722 bell723
cnot a2 bell723
measure bell723
cnot bell723 bell722
cnot bell722 b6
H bell722
measure bell722
cz bell722 a2
H bell724
cnot bell724 bell725
cnot a2 bell725
measure bell725
cnot bell725 bell724
cnot bell724 b5
H bell724
measure bell724
cz bell724 a2
H bell726
cnot bell726 bell727
cnot a2 bell727
measure bell727
cnot bell727 bell726
cnot bell726 b4
H bell726
measure bell726
cz bell726 a2
H bell728
cnot bell728 bell729
cnot a2 bell729
measure bell729
cnot bell729 bell728
cnot bell728 b3
H bell728
measure bell728
cz bell728 a2
H bell730
cnot bell730 bell731
cnot a2 bell731
measure bell731
cnot bell731 bell730
cnot bell730 b2
H bell730
measure bell730
cz bell730 a2
H bell732
cnot bell732 bell733
cnot a1 bell733
measure bell733
cnot bell733 bell732
cnot bell732 b1
H bell732
measure bell732
cz bell732 a1
cnot a1 b0
H bell734
cnot bell734 bell735
cnot a2 bell735
measure bell735
cnot bell735 bell734
cnot bell734 a9
H bell734
measure bell734
cz bell734 a2
H bell736
cnot bell736 bell737
cnot a2 bell737
measure bell737
cnot bell737 bell736
cnot bell736 a8
H bell736
measure bell736
cz bell736 a2
H bell738
cnot bell738 bell739
cnot a2 bell739
measure bell739
cnot bell739 bell738
cnot bell738 a7
H bell738
measure bell738
cz bell738 a2
H bell740
cnot bell740 bell741
cnot a2 bell741
measure bell741
cnot bell741 bell740
cnot bell740 a6
H bell740
measure bell740
cz bell740 a2
H bell742
cnot bell742 bell743
cnot a2 bell743
measure bell743
cnot bell743 bell742
cnot bell742 a5
cnot bell742 a4
H bell742
measure bell742
cz bell742 a2
H bell744
cnot bell744 bell745
cnot a2 bell745
measure bell745
cnot bell745 bell744
cnot bell744 a3
H bell744
measure bell744
cz bell744 a2
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
reset bell508
reset bell509
reset bell510
reset bell511
reset bell512
reset bell513
reset bell514
reset bell515
reset bell516
reset bell517
reset bell518
reset bell519
reset bell520
reset bell521
reset bell522
reset bell523
reset bell524
reset bell525
reset bell526
reset bell527
reset bell528
reset bell529
reset bell530
reset bell531
reset bell532
reset bell533
reset bell534
reset bell535
reset bell536
reset bell537
reset bell538
reset bell539
reset bell540
reset bell541
reset bell542
reset bell543
reset bell544
reset bell545
reset bell546
reset bell547
reset bell548
reset bell549
reset bell550
reset bell551
reset bell552
reset bell553
reset bell554
reset bell555
reset bell556
reset bell557
reset bell558
reset bell559
reset bell560
reset bell561
reset bell562
reset bell563
reset bell564
reset bell565
reset bell566
reset bell567
reset bell568
reset bell569
reset bell570
reset bell571
reset bell572
reset bell573
reset bell574
reset bell575
reset bell576
reset bell577
reset bell578
reset bell579
reset bell580
reset bell581
reset bell582
reset bell583
reset bell584
reset bell585
reset bell586
reset bell587
reset bell588
reset bell589
reset bell590
reset bell591
reset bell592
reset bell593
reset bell594
reset bell595
reset bell596
reset bell597
reset bell598
reset bell599
reset bell600
reset bell601
reset bell602
reset bell603
reset bell604
reset bell605
reset bell606
reset bell607
reset bell608
reset bell609
reset bell610
reset bell611
reset bell612
reset bell613
reset bell614
reset bell615
reset bell616
reset bell617
reset bell618
reset bell619
reset bell620
reset bell621
reset bell622
reset bell623
reset bell624
reset bell625
reset bell626
reset bell627
reset bell628
reset bell629
reset bell630
reset bell631
reset bell632
reset bell633
reset bell634
reset bell635
reset bell636
reset bell637
reset bell638
reset bell639
reset bell640
reset bell641
reset bell642
reset bell643
reset bell644
reset bell645
reset bell646
reset bell647
reset bell648
reset bell649
reset bell650
reset bell651
reset bell652
reset bell653
reset bell654
reset bell655
reset bell656
reset bell657
reset bell658
reset bell659
reset bell660
reset bell661
reset bell662
reset bell663
reset bell664
reset bell665
reset bell666
reset bell667
reset bell668
reset bell669
reset bell670
reset bell671
reset bell672
reset bell673
reset bell674
reset bell675
reset bell676
reset bell677
reset bell678
reset bell679
reset bell680
reset bell681
reset bell682
reset bell683
reset bell684
reset bell685
reset bell686
reset bell687
reset bell688
reset bell689
reset bell690
reset bell691
reset bell692
reset bell693
reset bell694
reset bell695
reset bell696
reset bell697
reset bell698
reset bell699
reset bell700
reset bell701
reset bell702
reset bell703
reset bell704
reset bell705
reset bell706
reset bell707
reset bell708
reset bell709
reset bell710
reset bell711
reset bell712
reset bell713
reset bell714
reset bell715
reset bell716
reset bell717
reset bell718
reset bell719
reset bell720
reset bell721
reset bell722
reset bell723
reset bell724
reset bell725
reset bell726
reset bell727
reset bell728
reset bell729
reset bell730
reset bell731
reset bell732
reset bell733
reset bell734
reset bell735
reset bell736
reset bell737
reset bell738
reset bell739
reset bell740
reset bell741
reset bell742
reset bell743
reset bell744
reset bell745
END
