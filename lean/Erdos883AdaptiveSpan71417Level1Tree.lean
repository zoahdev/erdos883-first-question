import Erdos883AdaptiveSpan71417Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength71417_1 : adaptiveNumericSpans71417_1.length = 581 := by decide +kernel
theorem adaptiveSpanEvenCache71417_1 : adaptiveSpanEven71417_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain71417_1 : adaptiveSpanEven71417_1.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanEvenEntries71417_1 : adaptiveSpanEven71417_1.spans = coreEvenSpans 35709 0 adaptiveNumericSpans71417_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache71417_1 : adaptiveSpanWhole71417_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain71417_1 : adaptiveSpanWhole71417_1.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanWholeEntries71417_1 : adaptiveSpanWhole71417_1.spans = coreWholeSpans 0 adaptiveNumericSpans71417_1 := by
  decide +kernel
end Erdos883Verified
