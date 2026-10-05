import Erdos883AdaptiveSpan71417Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength71417_8 : adaptiveNumericSpans71417_8.length = 581 := by decide +kernel
theorem adaptiveSpanEvenCache71417_8 : adaptiveSpanEven71417_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain71417_8 : adaptiveSpanEven71417_8.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanEvenEntries71417_8 : adaptiveSpanEven71417_8.spans = coreEvenSpans 35709 0 adaptiveNumericSpans71417_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache71417_8 : adaptiveSpanWhole71417_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain71417_8 : adaptiveSpanWhole71417_8.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanWholeEntries71417_8 : adaptiveSpanWhole71417_8.spans = coreWholeSpans 0 adaptiveNumericSpans71417_8 := by
  decide +kernel
end Erdos883Verified
