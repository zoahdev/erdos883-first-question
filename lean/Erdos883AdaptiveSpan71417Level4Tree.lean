import Erdos883AdaptiveSpan71417Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength71417_4 : adaptiveNumericSpans71417_4.length = 581 := by decide +kernel
theorem adaptiveSpanEvenCache71417_4 : adaptiveSpanEven71417_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain71417_4 : adaptiveSpanEven71417_4.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanEvenEntries71417_4 : adaptiveSpanEven71417_4.spans = coreEvenSpans 35709 0 adaptiveNumericSpans71417_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache71417_4 : adaptiveSpanWhole71417_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain71417_4 : adaptiveSpanWhole71417_4.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanWholeEntries71417_4 : adaptiveSpanWhole71417_4.spans = coreWholeSpans 0 adaptiveNumericSpans71417_4 := by
  decide +kernel
end Erdos883Verified
