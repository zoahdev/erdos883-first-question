import Erdos883AdaptiveSpan71417Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength71417_2 : adaptiveNumericSpans71417_2.length = 581 := by decide +kernel
theorem adaptiveSpanEvenCache71417_2 : adaptiveSpanEven71417_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain71417_2 : adaptiveSpanEven71417_2.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanEvenEntries71417_2 : adaptiveSpanEven71417_2.spans = coreEvenSpans 35709 0 adaptiveNumericSpans71417_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache71417_2 : adaptiveSpanWhole71417_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain71417_2 : adaptiveSpanWhole71417_2.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanWholeEntries71417_2 : adaptiveSpanWhole71417_2.spans = coreWholeSpans 0 adaptiveNumericSpans71417_2 := by
  decide +kernel
end Erdos883Verified
