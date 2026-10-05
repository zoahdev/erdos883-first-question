import Erdos883AdaptiveCertificate1310Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1310_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 12804040032829629204419657835294761900180861463625232864774048978662993693887888496914620515844657591784783108403942206352858675352176811164952575678641753628340368225203896304982507622354379230997028376805577294735673223147469165156314027486077602698596722494655561394689954031395084063161490341952
def adaptiveNumericSpans1310_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1310_0Chunk0].flatten
def adaptiveSpanEven1310_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 655 0 adaptiveNumericSpans1310_0)
def adaptiveSpanWhole1310_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1310_0)
theorem adaptiveSpanNumericCheck1310_0 : coreNumericSpansCheck 1287 6 480 1155 adaptiveNumericSpans1310_0 adaptiveRows1310 = true := by decide +kernel
theorem adaptiveSpanEvenCache1310_0 : adaptiveSpanEven1310_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1310_0 : adaptiveSpanEven1310_0.domainCheck 655 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1310_0 : adaptiveSpanEven1310_0.spans = coreEvenSpans 655 0 adaptiveNumericSpans1310_0 := by decide +kernel
theorem adaptiveSpanWholeCache1310_0 : adaptiveSpanWhole1310_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1310_0 : adaptiveSpanWhole1310_0.domainCheck 655 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1310_0 : adaptiveSpanWhole1310_0.spans = coreWholeSpans 0 adaptiveNumericSpans1310_0 := by decide +kernel
end Erdos883Verified
