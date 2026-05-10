import MeirMoser.Certificate
import MeirMoser.CalibratedScheduler
import MeirMoser.MainTheorem

namespace MeirMoser.Certificates.WarmStartN100

open MeirMoser

def container : Rect := { x0 := (0 : ℚ) / (1 : ℚ), y0 := (0 : ℚ) / (1 : ℚ), x1 := (1 : ℚ) / (1 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num }

def placed : List PlacedRect := [
  { n := 1, x0 := (0 : ℚ) / (1 : ℚ), y0 := (0 : ℚ) / (1 : ℚ), rotated := false },
  { n := 2, x0 := (0 : ℚ) / (1 : ℚ), y0 := (1 : ℚ) / (2 : ℚ), rotated := true },
  { n := 3, x0 := (1 : ℚ) / (3 : ℚ), y0 := (1 : ℚ) / (2 : ℚ), rotated := true },
  { n := 4, x0 := (7 : ℚ) / (12 : ℚ), y0 := (1 : ℚ) / (2 : ℚ), rotated := false },
  { n := 5, x0 := (5 : ℚ) / (6 : ℚ), y0 := (1 : ℚ) / (2 : ℚ), rotated := true },
  { n := 6, x0 := (1 : ℚ) / (3 : ℚ), y0 := (5 : ℚ) / (6 : ℚ), rotated := true },
  { n := 7, x0 := (10 : ℚ) / (21 : ℚ), y0 := (5 : ℚ) / (6 : ℚ), rotated := true },
  { n := 8, x0 := (7 : ℚ) / (12 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := true },
  { n := 9, x0 := (101 : ℚ) / (168 : ℚ), y0 := (33 : ℚ) / (40 : ℚ), rotated := true },
  { n := 10, x0 := (25 : ℚ) / (36 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := true },
  { n := 11, x0 := (589 : ℚ) / (840 : ℚ), y0 := (4 : ℚ) / (5 : ℚ), rotated := true },
  { n := 12, x0 := (589 : ℚ) / (840 : ℚ), y0 := (49 : ℚ) / (55 : ℚ), rotated := true },
  { n := 13, x0 := (8497 : ℚ) / (10920 : ℚ), y0 := (49 : ℚ) / (55 : ℚ), rotated := true },
  { n := 14, x0 := (659 : ℚ) / (840 : ℚ), y0 := (4 : ℚ) / (5 : ℚ), rotated := true },
  { n := 15, x0 := (101 : ℚ) / (168 : ℚ), y0 := (337 : ℚ) / (360 : ℚ), rotated := false },
  { n := 16, x0 := (311 : ℚ) / (396 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := true },
  { n := 17, x0 := (5683 : ℚ) / (6732 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := true },
  { n := 18, x0 := (673 : ℚ) / (748 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := false },
  { n := 19, x0 := (673 : ℚ) / (748 : ℚ), y0 := (143 : ℚ) / (190 : ℚ), rotated := false },
  { n := 20, x0 := (13535 : ℚ) / (14212 : ℚ), y0 := (143 : ℚ) / (190 : ℚ), rotated := true },
  { n := 21, x0 := (143 : ℚ) / (168 : ℚ), y0 := (129 : ℚ) / (170 : ℚ), rotated := false },
  { n := 22, x0 := (6431 : ℚ) / (6732 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), rotated := true },
  { n := 23, x0 := (151 : ℚ) / (168 : ℚ), y0 := (61 : ℚ) / (76 : ℚ), rotated := false },
  { n := 24, x0 := (143 : ℚ) / (168 : ℚ), y0 := (752 : ℚ) / (935 : ℚ), rotated := false },
  { n := 25, x0 := (143 : ℚ) / (168 : ℚ), y0 := (3947 : ℚ) / (4675 : ℚ), rotated := false },
  { n := 26, x0 := (311 : ℚ) / (396 : ℚ), y0 := (61 : ℚ) / (80 : ℚ), rotated := false },
  { n := 27, x0 := (3641 : ℚ) / (3864 : ℚ), y0 := (61 : ℚ) / (76 : ℚ), rotated := false },
  { n := 28, x0 := (3641 : ℚ) / (3864 : ℚ), y0 := (223 : ℚ) / (266 : ℚ), rotated := false },
  { n := 29, x0 := (187 : ℚ) / (280 : ℚ), y0 := (337 : ℚ) / (360 : ℚ), rotated := true },
  { n := 30, x0 := (3743 : ℚ) / (4200 : ℚ), y0 := (385 : ℚ) / (456 : ℚ), rotated := false },
  { n := 31, x0 := (8497 : ℚ) / (10920 : ℚ), y0 := (692 : ℚ) / (715 : ℚ), rotated := false },
  { n := 32, x0 := (274327 : ℚ) / (338520 : ℚ), y0 := (692 : ℚ) / (715 : ℚ), rotated := true },
  { n := 33, x0 := (1043479 : ℚ) / (1241240 : ℚ), y0 := (692 : ℚ) / (715 : ℚ), rotated := true },
  { n := 34, x0 := (187 : ℚ) / (280 : ℚ), y0 := (10133 : ℚ) / (10440 : ℚ), rotated := false },
  { n := 35, x0 := (3883 : ℚ) / (4200 : ℚ), y0 := (6733 : ℚ) / (7714 : ℚ), rotated := false },
  { n := 36, x0 := (4241 : ℚ) / (5148 : ℚ), y0 := (61 : ℚ) / (80 : ℚ), rotated := true },
  { n := 37, x0 := (3743 : ℚ) / (4200 : ℚ), y0 := (12391 : ℚ) / (14136 : ℚ), rotated := false },
  { n := 38, x0 := (3319 : ℚ) / (4760 : ℚ), y0 := (643 : ℚ) / (660 : ℚ), rotated := false },
  { n := 39, x0 := (65441 : ℚ) / (90440 : ℚ), y0 := (643 : ℚ) / (660 : ℚ), rotated := true },
  { n := 40, x0 := (33851 : ℚ) / (45220 : ℚ), y0 := (643 : ℚ) / (660 : ℚ), rotated := true },
  { n := 41, x0 := (10 : ℚ) / (21 : ℚ), y0 := (41 : ℚ) / (42 : ℚ), rotated := false },
  { n := 42, x0 := (431 : ℚ) / (861 : ℚ), y0 := (41 : ℚ) / (42 : ℚ), rotated := true },
  { n := 43, x0 := (19394 : ℚ) / (37023 : ℚ), y0 := (41 : ℚ) / (42 : ℚ), rotated := true },
  { n := 44, x0 := (890359 : ℚ) / (1629012 : ℚ), y0 := (41 : ℚ) / (42 : ℚ), rotated := true },
  { n := 45, x0 := (3779 : ℚ) / (3864 : ℚ), y0 := (223 : ℚ) / (266 : ℚ), rotated := true },
  { n := 46, x0 := (3779 : ℚ) / (3864 : ℚ), y0 := (10301 : ℚ) / (11970 : ℚ), rotated := false },
  { n := 47, x0 := (18359763 : ℚ) / (21101080 : ℚ), y0 := (107297 : ℚ) / (121550 : ℚ), rotated := true },
  { n := 48, x0 := (9277 : ℚ) / (10920 : ℚ), y0 := (107297 : ℚ) / (121550 : ℚ), rotated := true },
  { n := 49, x0 := (9277 : ℚ) / (10920 : ℚ), y0 := (2635903 : ℚ) / (2917200 : ℚ), rotated := false },
  { n := 50, x0 := (34057 : ℚ) / (34776 : ℚ), y0 := (61 : ℚ) / (76 : ℚ), rotated := false },
  { n := 51, x0 := (659 : ℚ) / (840 : ℚ), y0 := (61 : ℚ) / (70 : ℚ), rotated := false },
  { n := 52, x0 := (11483 : ℚ) / (14280 : ℚ), y0 := (61 : ℚ) / (70 : ℚ), rotated := true },
  { n := 53, x0 := (622879 : ℚ) / (756840 : ℚ), y0 := (61 : ℚ) / (70 : ℚ), rotated := true },
  { n := 54, x0 := (13898389 : ℚ) / (24435180 : ℚ), y0 := (41 : ℚ) / (42 : ℚ), rotated := true },
  { n := 55, x0 := (4003 : ℚ) / (4200 : ℚ), y0 := (6733 : ℚ) / (7714 : ℚ), rotated := false },
  { n := 56, x0 := (3883 : ℚ) / (4200 : ℚ), y0 := (385 : ℚ) / (456 : ℚ), rotated := true },
  { n := 57, x0 := (44873 : ℚ) / (46200 : ℚ), y0 := (496117 : ℚ) / (562590 : ℚ), rotated := false },
  { n := 58, x0 := (4003 : ℚ) / (4200 : ℚ), y0 := (27483 : ℚ) / (30856 : ℚ), rotated := false },
  { n := 59, x0 := (118187 : ℚ) / (121800 : ℚ), y0 := (7334344 : ℚ) / (8157555 : ℚ), rotated := false },
  { n := 60, x0 := (142691 : ℚ) / (155400 : ℚ), y0 := (125051 : ℚ) / (138852 : ℚ), rotated := false },
  { n := 61, x0 := (48427 : ℚ) / (51800 : ℚ), y0 := (125051 : ℚ) / (138852 : ℚ), rotated := false },
  { n := 62, x0 := (34057 : ℚ) / (34776 : ℚ), y0 := (3187 : ℚ) / (3876 : ℚ), rotated := false },
  { n := 63, x0 := (3005847 : ℚ) / (3159800 : ℚ), y0 := (1652353 : ℚ) / (1820504 : ℚ), rotated := false },
  { n := 64, x0 := (48427 : ℚ) / (51800 : ℚ), y0 := (3946007 : ℚ) / (4304412 : ℚ), rotated := false },
  { n := 65, x0 := (112796213 : ℚ) / (126606480 : ℚ), y0 := (12763 : ℚ) / (14136 : ℚ), rotated := false },
  { n := 66, x0 := (18359763 : ℚ) / (21101080 : ℚ), y0 := (5164509 : ℚ) / (5712850 : ℚ), rotated := false },
  { n := 67, x0 := (22948801 : ℚ) / (25321296 : ℚ), y0 := (7766963 : ℚ) / (8469972 : ℚ), rotated := false },
  { n := 68, x0 := (56038429 : ℚ) / (63303240 : ℚ), y0 := (47583 : ℚ) / (51832 : ℚ), rotated := false },
  { n := 69, x0 := (18359763 : ℚ) / (21101080 : ℚ), y0 := (351734953 : ℚ) / (382760950 : ℚ), rotated := false },
  { n := 70, x0 := (2868533 : ℚ) / (4887036 : ℚ), y0 := (41 : ℚ) / (42 : ℚ), rotated := true },
  { n := 71, x0 := (9277 : ℚ) / (10920 : ℚ), y0 := (2694247 : ℚ) / (2917200 : ℚ), rotated := false },
  { n := 72, x0 := (9277 : ℚ) / (10920 : ℚ), y0 := (8204291 : ℚ) / (8751600 : ℚ), rotated := true },
  { n := 73, x0 := (1562890963 : ℚ) / (1696526832 : ℚ), y0 := (7766963 : ℚ) / (8469972 : ℚ), rotated := true },
  { n := 74, x0 := (1562890963 : ℚ) / (1696526832 : ℚ), y0 := (575458271 : ℚ) / (618307956 : ℚ), rotated := false },
  { n := 75, x0 := (9277 : ℚ) / (10920 : ℚ), y0 := (8325841 : ℚ) / (8751600 : ℚ), rotated := true },
  { n := 76, x0 := (178993 : ℚ) / (207480 : ℚ), y0 := (8325841 : ℚ) / (8751600 : ℚ), rotated := true },
  { n := 77, x0 := (688141 : ℚ) / (797160 : ℚ), y0 := (8204291 : ℚ) / (8751600 : ℚ), rotated := true },
  { n := 78, x0 := (7094833 : ℚ) / (7186200 : ℚ), y0 := (7334344 : ℚ) / (8157555 : ℚ), rotated := true },
  { n := 79, x0 := (7094833 : ℚ) / (7186200 : ℚ), y0 := (193412129 : ℚ) / (212096430 : ℚ), rotated := false },
  { n := 80, x0 := (27504023 : ℚ) / (28438200 : ℚ), y0 := (29881213 : ℚ) / (32630220 : ℚ), rotated := false },
  { n := 81, x0 := (393891 : ℚ) / (414400 : ℚ), y0 := (13446387 : ℚ) / (14564032 : ℚ), rotated := false },
  { n := 82, x0 := (58675229047 : ℚ) / (62771492784 : ℚ), y0 := (260794867 : ℚ) / (279786780 : ℚ), rotated := false },
  { n := 83, x0 := (22948801 : ℚ) / (25321296 : ℚ), y0 := (12763 : ℚ) / (14136 : ℚ), rotated := true },
  { n := 84, x0 := (55719001 : ℚ) / (56876400 : ℚ), y0 := (313701335 : ℚ) / (339354288 : ℚ), rotated := false },
  { n := 85, x0 := (32319571 : ℚ) / (33566400 : ℚ), y0 := (272556497 : ℚ) / (293671980 : ℚ), rotated := false },
  { n := 86, x0 := (2437070137319 : ℚ) / (2573631204144 : ℚ), y0 := (558583883 : ℚ) / (597125312 : ℚ), rotated := false },
  { n := 87, x0 := (56969359 : ℚ) / (63303240 : ℚ), y0 := (33538966 : ℚ) / (35997381 : ℚ), rotated := false },
  { n := 88, x0 := (1287924727 : ℚ) / (1455974520 : ℚ), y0 := (3335059 : ℚ) / (3576408 : ℚ), rotated := false },
  { n := 89, x0 := (289329 : ℚ) / (292600 : ℚ), y0 := (496117 : ℚ) / (562590 : ℚ), rotated := true },
  { n := 90, x0 := (29647043 : ℚ) / (33090330 : ℚ), y0 := (2987426389 : ℚ) / (3167769528 : ℚ), rotated := false },
  { n := 91, x0 := (9004414 : ℚ) / (9927099 : ℚ), y0 := (2987426389 : ℚ) / (3167769528 : ℚ), rotated := false },
  { n := 92, x0 := (1301929 : ℚ) / (1418157 : ℚ), y0 := (14592559427 : ℚ) / (15457698900 : ℚ), rotated := false },
  { n := 93, x0 := (3883 : ℚ) / (4200 : ℚ), y0 := (344 : ℚ) / (399 : ℚ), rotated := false },
  { n := 94, x0 := (9004414 : ℚ) / (9927099 : ℚ), y0 := (69502749329 : ℚ) / (72858699144 : ℚ), rotated := false },
  { n := 95, x0 := (5269375 : ℚ) / (5672628 : ℚ), y0 := (21925760741 : ℚ) / (23222302740 : ℚ), rotated := false },
  { n := 96, x0 := (232787 : ℚ) / (265720 : ℚ), y0 := (300396659 : ℚ) / (318300312 : ℚ), rotated := false },
  { n := 97, x0 := (2826659 : ℚ) / (3188640 : ℚ), y0 := (39289081561 : ℚ) / (41181003864 : ℚ), rotated := false },
  { n := 98, x0 := (277374563 : ℚ) / (309298080 : ℚ), y0 := (39289081561 : ℚ) / (41181003864 : ℚ), rotated := false },
  { n := 99, x0 := (277374563 : ℚ) / (309298080 : ℚ), y0 := (13235017099 : ℚ) / (13727001288 : ℚ), rotated := false },
  { n := 100, x0 := (285509 : ℚ) / (326040 : ℚ), y0 := (29456776235 : ℚ) / (30875130264 : ℚ), rotated := false }
]

def lrp : Rect := { x0 := (55719001 : ℚ) / (56876400 : ℚ), y0 := (27003967763 : ℚ) / (28845114480 : ℚ), x1 := (56396101 : ℚ) / (56876400 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num }

def normalBoxes : List NormalBoxRecord := [
  
]

def endpointBoxes : List Rect := [
  { x0 := (208552879 : ℚ) / (346979556 : ℚ), y0 := (41 : ℚ) / (42 : ℚ), x1 := (101 : ℚ) / (168 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (3319 : ℚ) / (4760 : ℚ), y0 := (8579 : ℚ) / (8580 : ℚ), x1 := (33851 : ℚ) / (45220 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (8497 : ℚ) / (10920 : ℚ), y0 := (22859 : ℚ) / (22880 : ℚ), x1 := (1043479 : ℚ) / (1241240 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (659 : ℚ) / (840 : ℚ), y0 := (1621 : ℚ) / (1820 : ℚ), x1 := (622879 : ℚ) / (756840 : ℚ), y1 := (49 : ℚ) / (55 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (311 : ℚ) / (396 : ℚ), y0 := (1727 : ℚ) / (2160 : ℚ), x1 := (4241 : ℚ) / (5148 : ℚ), y1 := (4 : ℚ) / (5 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (162065 : ℚ) / (190476 : ℚ), y0 := (129 : ℚ) / (170 : ℚ), x1 := (143 : ℚ) / (168 : ℚ), y1 := (4 : ℚ) / (5 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (66499 : ℚ) / (76440 : ℚ), y0 := (107297 : ℚ) / (121550 : ℚ), x1 := (18359763 : ℚ) / (21101080 : ℚ), y1 := (8204291 : ℚ) / (8751600 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (112796213 : ℚ) / (126606480 : ℚ), y0 := (107297 : ℚ) / (121550 : ℚ), x1 := (3743 : ℚ) / (4200 : ℚ), y1 := (12763 : ℚ) / (14136 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (3743 : ℚ) / (4200 : ℚ), y0 := (3947 : ℚ) / (4675 : ℚ), x1 := (25 : ℚ) / (28 : ℚ), y1 := (385 : ℚ) / (456 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (9256459939 : ℚ) / (10206836640 : ℚ), y0 := (13235017099 : ℚ) / (13727001288 : ℚ), x1 := (1963714661 : ℚ) / (2165086560 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (1963714661 : ℚ) / (2165086560 : ℚ), y0 := (39289081561 : ℚ) / (41181003864 : ℚ), x1 := (9004414 : ℚ) / (9927099 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (856342015 : ℚ) / (933147306 : ℚ), y0 := (69502749329 : ℚ) / (72858699144 : ℚ), x1 := (1301929 : ℚ) / (1418157 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (23250245 : ℚ) / (25321296 : ℚ), y0 := (12763 : ℚ) / (14136 : ℚ), x1 := (142691 : ℚ) / (155400 : ℚ), y1 := (7766963 : ℚ) / (8469972 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (3883 : ℚ) / (4200 : ℚ), y0 := (32735 : ℚ) / (37506 : ℚ), x1 := (40591 : ℚ) / (43400 : ℚ), y1 := (6733 : ℚ) / (7714 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (58675229047 : ℚ) / (62771492784 : ℚ), y0 := (7766963 : ℚ) / (8469972 : ℚ), x1 := (48427 : ℚ) / (51800 : ℚ), y1 := (260794867 : ℚ) / (279786780 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (25059 : ℚ) / (26600 : ℚ), y0 := (385 : ℚ) / (456 : ℚ), x1 := (3641 : ℚ) / (3864 : ℚ), y1 := (6733 : ℚ) / (7714 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (34057 : ℚ) / (34776 : ℚ), y0 := (68219 : ℚ) / (81396 : ℚ), x1 := (1073155 : ℚ) / (1078056 : ℚ), y1 := (223 : ℚ) / (266 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (868813 : ℚ) / (869400 : ℚ), y0 := (61 : ℚ) / (76 : ℚ), x1 := (3863 : ℚ) / (3864 : ℚ), y1 := (223 : ℚ) / (266 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (3863 : ℚ) / (3864 : ℚ), y0 := (61 : ℚ) / (76 : ℚ), x1 := (2633221 : ℚ) / (2633400 : ℚ), y1 := (496117 : ℚ) / (562590 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (2633221 : ℚ) / (2633400 : ℚ), y0 := (61 : ℚ) / (76 : ℚ), x1 := (567678007 : ℚ) / (567709800 : ℚ), y1 := (7334344 : ℚ) / (8157555 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (567678007 : ℚ) / (567709800 : ℚ), y0 := (61 : ℚ) / (76 : ℚ), x1 := (298447 : ℚ) / (298452 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num },
    { x0 := (298447 : ℚ) / (298452 : ℚ), y0 := (7 : ℚ) / (10 : ℚ), x1 := (1 : ℚ) / (1 : ℚ), y1 := (1 : ℚ) / (1 : ℚ), hx := by norm_num, hy := by norm_num }
]

def widthChecks : List NormalWidthCheck := []

def state : TailState :=
  { t := 101,
    container := container,
    placed := placed,
    LRP := lrp,
    normalBoxes := normalBoxes,
    endpointBoxes := endpointBoxes }

def cParam : ℚ := (185955818417 : ℚ) / (2422989616320 : ℚ)
def RParam : ℚ := (1841146717 : ℚ) / (343394220 : ℚ)
def etaParam : ℚ := (12487787361314006833544309799461 : ℚ) / (9926184571964537849828391135600 : ℚ)

theorem finite_packing_valid : FinitePacking container placed := by
  native_decide

theorem warm_start_good :
    GoodTailState cParam RParam etaParam state widthChecks := by
  native_decide

/-- The container is the unit square. -/
theorem state_container_unit : state.container = unitSquare := by
  unfold state container unitSquare
  native_decide

/-- The placed prefix covers all indices 1, …, state.t − 1 = 1, …, 100. -/
theorem state_prefix_covers :
    ∀ n, 1 ≤ n → n < state.t → ∃ P ∈ state.placed, P.n = n := by
  native_decide

/-- The γ = 4/3 constraint `1 < γ < 3/2` in rational form. -/
theorem gamma_in_range : 1 * 3 < 4 ∧ 4 * 2 < 3 * 3 := by decide

/-- The hand-built state has `state.t ≥ 1`. -/
theorem state_t_pos : 1 ≤ state.t := by native_decide

/-- The LRP is contained in the container. -/
theorem state_LRP_in_container : state.container.contains state.LRP := by
  native_decide

/-- The LRP is interior-disjoint from each placed rectangle. -/
theorem state_LRP_disj :
    ∀ P ∈ state.placed, Rect.interiorDisjoint state.LRP P.toRect := by
  native_decide

/-- The c-parameter is strictly positive. -/
theorem state_c_pos : 0 < cParam := by
  unfold cParam; native_decide

/-- The R-parameter is strictly positive. -/
theorem state_R_pos : 0 < RParam := by
  unfold RParam; native_decide

/-- The R-parameter satisfies `1 ≤ R`.
    Numerically: R ≈ 5.36, so this is comfortably true. This discharges
    the threaded `h_R_ge_one` hypothesis (formerly the
    `balanced_R_ge_one_axiom`). -/
theorem state_R_ge_one : (1 : ℚ) ≤ RParam := by
  unfold RParam; native_decide

/-- The R-parameter satisfies `(R - 1)² ≥ R`, equivalently `R ≥ φ²` (the
    square of the golden ratio, ≈ 2.618). This discharges the threaded
    `h_R_squared` hypothesis used by the proved room-invariant theorem
    `balanced_room_invariant_proved_step`. Numerically: `(R-1)² ≈ 19.0 ≫ R ≈ 5.36`. -/
theorem state_R_squared : RParam ≤ (RParam - 1) * (RParam - 1) := by
  unfold RParam; native_decide

/-- The certificate satisfies `R ≤ c · t`, so `base_LRP_fits` applies at S.
    Numerically: c ≈ 0.0767, R ≈ 5.361, t = 101 ⇒ c · t ≈ 7.752 ≥ R. -/
theorem state_t_large : (RParam : ℚ) ≤ cParam * (state.t : ℕ) := by
  unfold RParam cParam state; native_decide

/-- THE MAIN INSTANTIATED THEOREM:
    The Moser sequence packs into the unit square (modulo the single
    remaining project axiom `balanced_c_share_positive_axiom` in
    `MeirMoser.AllStepsSucceedProof`). Conclusion is
    `MoserPacksFrom 1 unitSquare`. -/
theorem meir_moser_packs_unit_square :
    MoserPacksFrom 1 unitSquare :=
  meir_moser_packing_from_certificate
    4 3 cParam RParam etaParam gamma_in_range
    state widthChecks warm_start_good
    state_container_unit
    state_prefix_covers
    state_c_pos
    state_R_pos
    state_R_ge_one
    state_R_squared
    state_t_large
    state_t_pos
    state_LRP_in_container
    state_LRP_disj

end MeirMoser.Certificates.WarmStartN100
