import Erdos883AdaptiveCertificate1795Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1795_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 17565957624563391129189741970183195329321355699363595291191903886271472233560485167768182207688152807271725223307744428373371926562587953727541789838227551986786053810543656902186152220575915233134991074214299475154219345178052691509171843985974973726265366021442590000783415242042364705587211534400
def adaptiveNumericSpans1795_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1795_0Chunk0].flatten
def adaptiveSpanEven1795_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 898 0 adaptiveNumericSpans1795_0)
def adaptiveSpanWhole1795_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1795_0)
theorem adaptiveSpanNumericCheck1795_0 : coreNumericSpansCheck 1752 6 480 1155 adaptiveNumericSpans1795_0 adaptiveRows1795 = true := by decide +kernel
theorem adaptiveSpanEvenCache1795_0 : adaptiveSpanEven1795_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1795_0 : adaptiveSpanEven1795_0.domainCheck 898 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1795_0 : adaptiveSpanEven1795_0.spans = coreEvenSpans 898 0 adaptiveNumericSpans1795_0 := by decide +kernel
theorem adaptiveSpanWholeCache1795_0 : adaptiveSpanWhole1795_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1795_0 : adaptiveSpanWhole1795_0.domainCheck 898 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1795_0 : adaptiveSpanWhole1795_0.spans = coreWholeSpans 0 adaptiveNumericSpans1795_0 := by decide +kernel
def adaptiveNumericSpans1795_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 10931322266791939218831085174276169878373332874239024058287289345345231266908863256650436022512099155443207613599133526038709097719946225539245386039983073682574827653432842896809318471790688192720521598100604444682177295621420895212404864
def adaptiveNumericSpans1795_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1795_1Chunk0].flatten
def adaptiveSpanEven1795_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 898 0 adaptiveNumericSpans1795_1)
def adaptiveSpanWhole1795_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1795_1)
theorem adaptiveSpanNumericCheck1795_1 : coreNumericSpansCheck 1752 6 240 385 adaptiveNumericSpans1795_1 adaptiveRows1795 = true := by decide +kernel
theorem adaptiveSpanEvenCache1795_1 : adaptiveSpanEven1795_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1795_1 : adaptiveSpanEven1795_1.domainCheck 898 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1795_1 : adaptiveSpanEven1795_1.spans = coreEvenSpans 898 0 adaptiveNumericSpans1795_1 := by decide +kernel
theorem adaptiveSpanWholeCache1795_1 : adaptiveSpanWhole1795_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1795_1 : adaptiveSpanWhole1795_1.domainCheck 898 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1795_1 : adaptiveSpanWhole1795_1.spans = coreWholeSpans 0 adaptiveNumericSpans1795_1 := by decide +kernel
def adaptiveNumericSpans1795_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 10931322266791939218831085174276169878373332874239024058287289345345231266908863256650436022512099155443207613599133526038709097719946225539245386039983198013443215649782887634428223679172276761349151454137344713957542159397134291871727744
def adaptiveNumericSpans1795_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1795_2Chunk0].flatten
def adaptiveSpanEven1795_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 898 0 adaptiveNumericSpans1795_2)
def adaptiveSpanWhole1795_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1795_2)
theorem adaptiveSpanNumericCheck1795_2 : coreNumericSpansCheck 1752 6 720 1001 adaptiveNumericSpans1795_2 adaptiveRows1795 = true := by decide +kernel
theorem adaptiveSpanEvenCache1795_2 : adaptiveSpanEven1795_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1795_2 : adaptiveSpanEven1795_2.domainCheck 898 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1795_2 : adaptiveSpanEven1795_2.spans = coreEvenSpans 898 0 adaptiveNumericSpans1795_2 := by decide +kernel
theorem adaptiveSpanWholeCache1795_2 : adaptiveSpanWhole1795_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1795_2 : adaptiveSpanWhole1795_2.domainCheck 898 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1795_2 : adaptiveSpanWhole1795_2.spans = coreWholeSpans 0 adaptiveNumericSpans1795_2 := by decide +kernel
def adaptiveNumericSpans1795_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 28227405590752194300491217838096875886187078848570696963774793085444399380479251049123134613605253471755917038720880467023865573236565870462712062088168162210704000300697453939807067679126058866390362209999456975842094657924180271049880472677213211053113561372033582180953392967197811458652877088217220579988880030096753470896636744474342796902613520171925632
def adaptiveNumericSpans1795_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1795_3Chunk0].flatten
def adaptiveSpanEven1795_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 898 0 adaptiveNumericSpans1795_3)
def adaptiveSpanWhole1795_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1795_3)
theorem adaptiveSpanNumericCheck1795_3 : coreNumericSpansCheck 1752 6 120 143 adaptiveNumericSpans1795_3 adaptiveRows1795 = true := by decide +kernel
theorem adaptiveSpanEvenCache1795_3 : adaptiveSpanEven1795_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1795_3 : adaptiveSpanEven1795_3.domainCheck 898 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1795_3 : adaptiveSpanEven1795_3.spans = coreEvenSpans 898 0 adaptiveNumericSpans1795_3 := by decide +kernel
theorem adaptiveSpanWholeCache1795_3 : adaptiveSpanWhole1795_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1795_3 : adaptiveSpanWhole1795_3.domainCheck 898 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1795_3 : adaptiveSpanWhole1795_3.spans = coreWholeSpans 0 adaptiveNumericSpans1795_3 := by decide +kernel
def adaptiveNumericSpans1795_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 28227405590752194300491217838096875886187078848570696963774793085444399380479251049123134613605253471755917038720880467024113578807992830871841386226087344429836564382586112648521677464965287475034007509935591665915338291951285763476325028865644837163701034572633983444927287556880940747161922355307663273623706499607618419326188356708468383829820833615839360
def adaptiveNumericSpans1795_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1795_4Chunk0].flatten
def adaptiveSpanEven1795_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 898 0 adaptiveNumericSpans1795_4)
def adaptiveSpanWhole1795_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1795_4)
theorem adaptiveSpanNumericCheck1795_4 : coreNumericSpansCheck 1752 6 192 221 adaptiveNumericSpans1795_4 adaptiveRows1795 = true := by decide +kernel
theorem adaptiveSpanEvenCache1795_4 : adaptiveSpanEven1795_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1795_4 : adaptiveSpanEven1795_4.domainCheck 898 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1795_4 : adaptiveSpanEven1795_4.spans = coreEvenSpans 898 0 adaptiveNumericSpans1795_4 := by decide +kernel
theorem adaptiveSpanWholeCache1795_4 : adaptiveSpanWhole1795_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1795_4 : adaptiveSpanWhole1795_4.domainCheck 898 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1795_4 : adaptiveSpanWhole1795_4.spans = coreWholeSpans 0 adaptiveNumericSpans1795_4 := by decide +kernel
def adaptiveNumericSpans1795_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 28227405590752194300491217838096875886187078848570696963774793085444399380479251049123134613605253471755917038720880467023833777653907383452421778028626170574586787702821965559336685828649012186647888710312357244586374053107179566555394100420464634876617772403089501809381869442019076685230532218304308636797915312948588241210468652512738158813738458870186112
def adaptiveNumericSpans1795_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1795_5Chunk0].flatten
def adaptiveSpanEven1795_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 898 0 adaptiveNumericSpans1795_5)
def adaptiveSpanWhole1795_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1795_5)
theorem adaptiveSpanNumericCheck1795_5 : coreNumericSpansCheck 1752 6 288 323 adaptiveNumericSpans1795_5 adaptiveRows1795 = true := by decide +kernel
theorem adaptiveSpanEvenCache1795_5 : adaptiveSpanEven1795_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1795_5 : adaptiveSpanEven1795_5.domainCheck 898 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1795_5 : adaptiveSpanEven1795_5.spans = coreEvenSpans 898 0 adaptiveNumericSpans1795_5 := by decide +kernel
theorem adaptiveSpanWholeCache1795_5 : adaptiveSpanWhole1795_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1795_5 : adaptiveSpanWhole1795_5.domainCheck 898 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1795_5 : adaptiveSpanWhole1795_5.spans = coreWholeSpans 0 adaptiveNumericSpans1795_5 := by decide +kernel
end Erdos883Verified
