import Erdos883AdaptiveCertificate3495Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans3495_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 86101614106532590883186547962610017769704109267957953917562782689721062870049566313551785120504103981512164571249015315614898595695894109518029604496553951465744812095288854289971500224904224022050454692038970520825996642649459056667536663713499147499424429279509992850024983771372416652032638159129792874970616503960678620225483132242623916722525104071113899147975396606788230857516804504625689746161389493002103160960
def adaptiveNumericSpans3495_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans3495_0Chunk0].flatten
def adaptiveSpanEven3495_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 1748 0 adaptiveNumericSpans3495_0)
def adaptiveSpanWhole3495_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3495_0)
theorem adaptiveSpanNumericCheck3495_0 : coreNumericSpansCheck 3329 7 480 1155 adaptiveNumericSpans3495_0 adaptiveRows3495 = true := by decide +kernel
theorem adaptiveSpanEvenCache3495_0 : adaptiveSpanEven3495_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3495_0 : adaptiveSpanEven3495_0.domainCheck 1748 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3495_0 : adaptiveSpanEven3495_0.spans = coreEvenSpans 1748 0 adaptiveNumericSpans3495_0 := by decide +kernel
theorem adaptiveSpanWholeCache3495_0 : adaptiveSpanWhole3495_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3495_0 : adaptiveSpanWhole3495_0.domainCheck 1748 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3495_0 : adaptiveSpanWhole3495_0.spans = coreWholeSpans 0 adaptiveNumericSpans3495_0 := by decide +kernel
def adaptiveNumericSpans3495_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 14 86101614106532590883186547962610017769704109267957953917562782689721062870049566313551785120504103981512164571249015315614898595695894109518029604496553951465744812095288854289971500224904224022050454692038970520825996642649459056667536663713499147499424429279509992850024983771372416652032638159129792874970616503960678620225483132275649302711749920653217765781297303556128823661297020793560240833810380382904090886272
def adaptiveNumericSpans3495_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans3495_1Chunk0].flatten
def adaptiveSpanEven3495_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 1748 0 adaptiveNumericSpans3495_1)
def adaptiveSpanWhole3495_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans3495_1)
theorem adaptiveSpanNumericCheck3495_1 : coreNumericSpansCheck 3329 7 240 385 adaptiveNumericSpans3495_1 adaptiveRows3495 = true := by decide +kernel
theorem adaptiveSpanEvenCache3495_1 : adaptiveSpanEven3495_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain3495_1 : adaptiveSpanEven3495_1.domainCheck 1748 = true := by decide +kernel
theorem adaptiveSpanEvenEntries3495_1 : adaptiveSpanEven3495_1.spans = coreEvenSpans 1748 0 adaptiveNumericSpans3495_1 := by decide +kernel
theorem adaptiveSpanWholeCache3495_1 : adaptiveSpanWhole3495_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain3495_1 : adaptiveSpanWhole3495_1.domainCheck 1748 = true := by decide +kernel
theorem adaptiveSpanWholeEntries3495_1 : adaptiveSpanWhole3495_1.spans = coreWholeSpans 0 adaptiveNumericSpans3495_1 := by decide +kernel
end Erdos883Verified
