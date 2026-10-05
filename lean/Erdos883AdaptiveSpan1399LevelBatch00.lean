import Erdos883AdaptiveCertificate1399Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1399_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 10729375426053128996294022961320427779861560323455002162742459361482060043237693581161503474777441064322769460609721617912766982133355403830619916329599062682689877364745770917618052931745123435655924848744085426252654971409765087410751144471270956811147694136285462592
def adaptiveNumericSpans1399_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1399_0Chunk0].flatten
def adaptiveSpanEven1399_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 700 0 adaptiveNumericSpans1399_0)
def adaptiveSpanWhole1399_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1399_0)
theorem adaptiveSpanNumericCheck1399_0 : coreNumericSpansCheck 1365 6 480 1155 adaptiveNumericSpans1399_0 adaptiveRows1399 = true := by decide +kernel
theorem adaptiveSpanEvenCache1399_0 : adaptiveSpanEven1399_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1399_0 : adaptiveSpanEven1399_0.domainCheck 700 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1399_0 : adaptiveSpanEven1399_0.spans = coreEvenSpans 700 0 adaptiveNumericSpans1399_0 := by decide +kernel
theorem adaptiveSpanWholeCache1399_0 : adaptiveSpanWhole1399_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1399_0 : adaptiveSpanWhole1399_0.domainCheck 700 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1399_0 : adaptiveSpanWhole1399_0.spans = coreWholeSpans 0 adaptiveNumericSpans1399_0 := by decide +kernel
def adaptiveNumericSpans1399_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 6 5267150679076342626097827508924384133474179169933249164029966513756130520301829310412757642833187759917695362928648069211653760881206230532126431018350455277026754840959211536512
def adaptiveNumericSpans1399_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1399_1Chunk0].flatten
def adaptiveSpanEven1399_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 700 0 adaptiveNumericSpans1399_1)
def adaptiveSpanWhole1399_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1399_1)
theorem adaptiveSpanNumericCheck1399_1 : coreNumericSpansCheck 1365 6 240 385 adaptiveNumericSpans1399_1 adaptiveRows1399 = true := by decide +kernel
theorem adaptiveSpanEvenCache1399_1 : adaptiveSpanEven1399_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1399_1 : adaptiveSpanEven1399_1.domainCheck 700 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1399_1 : adaptiveSpanEven1399_1.spans = coreEvenSpans 700 0 adaptiveNumericSpans1399_1 := by decide +kernel
theorem adaptiveSpanWholeCache1399_1 : adaptiveSpanWhole1399_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1399_1 : adaptiveSpanWhole1399_1.domainCheck 700 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1399_1 : adaptiveSpanWhole1399_1.spans = coreWholeSpans 0 adaptiveNumericSpans1399_1 := by decide +kernel
def adaptiveNumericSpans1399_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 6 5267150679076342626097827508924384133474179169933249164029966513756130520301829310412757642833187759917695362928648069211747243154505600509744280651320920442383479221975313809536
def adaptiveNumericSpans1399_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1399_2Chunk0].flatten
def adaptiveSpanEven1399_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 700 0 adaptiveNumericSpans1399_2)
def adaptiveSpanWhole1399_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1399_2)
theorem adaptiveSpanNumericCheck1399_2 : coreNumericSpansCheck 1365 6 720 1001 adaptiveNumericSpans1399_2 adaptiveRows1399 = true := by decide +kernel
theorem adaptiveSpanEvenCache1399_2 : adaptiveSpanEven1399_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1399_2 : adaptiveSpanEven1399_2.domainCheck 700 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1399_2 : adaptiveSpanEven1399_2.spans = coreEvenSpans 700 0 adaptiveNumericSpans1399_2 := by decide +kernel
theorem adaptiveSpanWholeCache1399_2 : adaptiveSpanWhole1399_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1399_2 : adaptiveSpanWhole1399_2.domainCheck 700 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1399_2 : adaptiveSpanWhole1399_2.spans = coreWholeSpans 0 adaptiveNumericSpans1399_2 := by decide +kernel
def adaptiveNumericSpans1399_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 21856123746469378247185043564452761415925349557459406441080253221334487147797516681827480518953676023980493375829664801011015863068805575280650517371041491240239190385818690788820759752918628488898994112364943502612014260569827482262109215137600109861171019928055614584644999017897515768441884495471022941731964994150264643141540294376369175311963553211088960
def adaptiveNumericSpans1399_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1399_3Chunk0].flatten
def adaptiveSpanEven1399_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 700 0 adaptiveNumericSpans1399_3)
def adaptiveSpanWhole1399_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1399_3)
theorem adaptiveSpanNumericCheck1399_3 : coreNumericSpansCheck 1365 6 120 143 adaptiveNumericSpans1399_3 adaptiveRows1399 = true := by decide +kernel
theorem adaptiveSpanEvenCache1399_3 : adaptiveSpanEven1399_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1399_3 : adaptiveSpanEven1399_3.domainCheck 700 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1399_3 : adaptiveSpanEven1399_3.spans = coreEvenSpans 700 0 adaptiveNumericSpans1399_3 := by decide +kernel
theorem adaptiveSpanWholeCache1399_3 : adaptiveSpanWhole1399_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1399_3 : adaptiveSpanWhole1399_3.domainCheck 700 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1399_3 : adaptiveSpanWhole1399_3.spans = coreWholeSpans 0 adaptiveNumericSpans1399_3 := by decide +kernel
def adaptiveNumericSpans1399_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 20 145736948588265927091445959342609110053429476364930073684088269044435500471766852123928699583071327416133128343699725887155250039134867831784270413420663670011538491946478489165207520971253071012494739066657632133869680505900755570427503255185563899433048691323539969006245342255539353785664732891172300249038188076737365177474486355001352241286536642904314197221542218281663010433614524370597769319284766478167251037245680908989189793765954181074992534348110369620572249091100981350067259889393877808520542737996557868890208192495596896870271613901773884655095612934616220891046720830389520741433408
def adaptiveNumericSpans1399_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1399_4Chunk0].flatten
def adaptiveSpanEven1399_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 700 0 adaptiveNumericSpans1399_4)
def adaptiveSpanWhole1399_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1399_4)
theorem adaptiveSpanNumericCheck1399_4 : coreNumericSpansCheck 1365 6 192 221 adaptiveNumericSpans1399_4 adaptiveRows1399 = true := by decide +kernel
theorem adaptiveSpanEvenCache1399_4 : adaptiveSpanEven1399_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1399_4 : adaptiveSpanEven1399_4.domainCheck 700 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1399_4 : adaptiveSpanEven1399_4.spans = coreEvenSpans 700 0 adaptiveNumericSpans1399_4 := by decide +kernel
theorem adaptiveSpanWholeCache1399_4 : adaptiveSpanWhole1399_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1399_4 : adaptiveSpanWhole1399_4.domainCheck 700 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1399_4 : adaptiveSpanWhole1399_4.spans = coreWholeSpans 0 adaptiveNumericSpans1399_4 := by decide +kernel
def adaptiveNumericSpans1399_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 26 604737737128218312091255049608738787831673068047854497087829658213929605899921131828838051216676164053631006892647349927552358327465830117208238891990562676280802059459392696789571742607653839649083953072097734197919071598627329355960426798870813633264587625661241285921056297154073103584432644895548206984184067129318775113037654629246460364890546179812089187000232663962458960112617860247271389315880430575240815757959650769180244588182047933722899669446772529101821687102471922519172079945852413508362072912216214816603700956186305441499583075169302963865332951208046814536522201398188279263120608433871269902983450460543513705727936574066221499885324145229714004903574005259436731170062539424622823064077900612203899192902977316025096996016350639997502215667516882812911222848
def adaptiveNumericSpans1399_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1399_5Chunk0].flatten
def adaptiveSpanEven1399_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 700 0 adaptiveNumericSpans1399_5)
def adaptiveSpanWhole1399_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1399_5)
theorem adaptiveSpanNumericCheck1399_5 : coreNumericSpansCheck 1365 6 288 323 adaptiveNumericSpans1399_5 adaptiveRows1399 = true := by decide +kernel
theorem adaptiveSpanEvenCache1399_5 : adaptiveSpanEven1399_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1399_5 : adaptiveSpanEven1399_5.domainCheck 700 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1399_5 : adaptiveSpanEven1399_5.spans = coreEvenSpans 700 0 adaptiveNumericSpans1399_5 := by decide +kernel
theorem adaptiveSpanWholeCache1399_5 : adaptiveSpanWhole1399_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1399_5 : adaptiveSpanWhole1399_5.domainCheck 700 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1399_5 : adaptiveSpanWhole1399_5.spans = coreWholeSpans 0 adaptiveNumericSpans1399_5 := by decide +kernel
end Erdos883Verified
