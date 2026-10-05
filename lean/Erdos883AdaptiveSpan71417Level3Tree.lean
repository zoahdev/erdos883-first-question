import Erdos883AdaptiveSpan71417Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength71417_3 : adaptiveNumericSpans71417_3.length = 581 := by decide +kernel
theorem adaptiveSpanEvenCache71417_3 : adaptiveSpanEven71417_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain71417_3 : adaptiveSpanEven71417_3.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanEvenEntries71417_3 : adaptiveSpanEven71417_3.spans = coreEvenSpans 35709 0 adaptiveNumericSpans71417_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache71417_3 : adaptiveSpanWhole71417_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain71417_3 : adaptiveSpanWhole71417_3.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanWholeEntries71417_3 : adaptiveSpanWhole71417_3.spans = coreWholeSpans 0 adaptiveNumericSpans71417_3 := by
  decide +kernel
end Erdos883Verified
