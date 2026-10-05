import Erdos883AdaptiveSpan71417Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength71417_6 : adaptiveNumericSpans71417_6.length = 581 := by decide +kernel
theorem adaptiveSpanEvenCache71417_6 : adaptiveSpanEven71417_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain71417_6 : adaptiveSpanEven71417_6.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanEvenEntries71417_6 : adaptiveSpanEven71417_6.spans = coreEvenSpans 35709 0 adaptiveNumericSpans71417_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache71417_6 : adaptiveSpanWhole71417_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain71417_6 : adaptiveSpanWhole71417_6.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanWholeEntries71417_6 : adaptiveSpanWhole71417_6.spans = coreWholeSpans 0 adaptiveNumericSpans71417_6 := by
  decide +kernel
end Erdos883Verified
