import Erdos883AdaptiveSpan71417Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength71417_0 : adaptiveNumericSpans71417_0.length = 581 := by decide +kernel
theorem adaptiveSpanEvenCache71417_0 : adaptiveSpanEven71417_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain71417_0 : adaptiveSpanEven71417_0.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanEvenEntries71417_0 : adaptiveSpanEven71417_0.spans = coreEvenSpans 35709 0 adaptiveNumericSpans71417_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache71417_0 : adaptiveSpanWhole71417_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain71417_0 : adaptiveSpanWhole71417_0.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanWholeEntries71417_0 : adaptiveSpanWhole71417_0.spans = coreWholeSpans 0 adaptiveNumericSpans71417_0 := by
  decide +kernel
end Erdos883Verified
