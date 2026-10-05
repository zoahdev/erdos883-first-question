import Erdos883AdaptiveCertificate3328Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans3328_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 81906040483501767605851147077755933446458875761908334292322092469820456542568005612720146245078333043189613339962543407060734787903683001569630026244767933417360681749929728664076326395129040683321101557178220420987238649882148608416472906610920947868177485533424970919613539718753458281195213450676031496203508136600838777648410776428038037437724434027485936070702782013695607281849049873658293453876049391473446092928
def adaptiveNumericSpans3328_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans3328_0Chunk0].flatten
def adaptiveSpanEven3328_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1664 0 adaptiveNumericSpans3328_0)
def adaptiveSpanWhole3328_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3328_0)
theorem adaptiveSpanNumericCheck3328_0 : coreNumericSpansCheck 3170 7 480 1155 adaptiveNumericSpans3328_0 adaptiveRows3328 = true := by decide +kernel
theorem adaptiveSpanEvenCache3328_0 : adaptiveSpanEven3328_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3328_0 : adaptiveSpanEven3328_0.domainCheck 1664 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3328_0 : adaptiveSpanEven3328_0.spans = coreEvenSpans 1664 0 adaptiveNumericSpans3328_0 := by decide +kernel
theorem adaptiveSpanWholeCache3328_0 : adaptiveSpanWhole3328_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3328_0 : adaptiveSpanWhole3328_0.domainCheck 1664 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3328_0 : adaptiveSpanWhole3328_0.spans = coreWholeSpans 0 adaptiveNumericSpans3328_0 := by decide +kernel
def adaptiveNumericSpans3328_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 64612473238884043844036274094572330931779685473098262151363847361524306853792612836712371793548759446107220039712269185682705360769706781772925338349071600930076784275757106200330770663432915626768998365973807841679352453903678566611128919125312383322718123272094863099711714593667652265127003716275200052962544303759778511861540605882183295656586713426580176846280839108270118903218176128
def adaptiveNumericSpans3328_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans3328_1Chunk0].flatten
def adaptiveSpanEven3328_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1664 0 adaptiveNumericSpans3328_1)
def adaptiveSpanWhole3328_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3328_1)
theorem adaptiveSpanNumericCheck3328_1 : coreNumericSpansCheck 3170 7 240 385 adaptiveNumericSpans3328_1 adaptiveRows3328 = true := by decide +kernel
theorem adaptiveSpanEvenCache3328_1 : adaptiveSpanEven3328_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3328_1 : adaptiveSpanEven3328_1.domainCheck 1664 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3328_1 : adaptiveSpanEven3328_1.spans = coreEvenSpans 1664 0 adaptiveNumericSpans3328_1 := by decide +kernel
theorem adaptiveSpanWholeCache3328_1 : adaptiveSpanWhole3328_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3328_1 : adaptiveSpanWhole3328_1.domainCheck 1664 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3328_1 : adaptiveSpanWhole3328_1.spans = coreWholeSpans 0 adaptiveNumericSpans3328_1 := by decide +kernel
end Erdos883Verified
