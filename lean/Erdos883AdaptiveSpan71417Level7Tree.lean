import Erdos883AdaptiveSpan71417Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength71417_7 : adaptiveNumericSpans71417_7.length = 581 := by decide +kernel
theorem adaptiveSpanEvenCache71417_7 : adaptiveSpanEven71417_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain71417_7 : adaptiveSpanEven71417_7.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanEvenEntries71417_7 : adaptiveSpanEven71417_7.spans = coreEvenSpans 35709 0 adaptiveNumericSpans71417_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache71417_7 : adaptiveSpanWhole71417_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain71417_7 : adaptiveSpanWhole71417_7.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanWholeEntries71417_7 : adaptiveSpanWhole71417_7.spans = coreWholeSpans 0 adaptiveNumericSpans71417_7 := by
  decide +kernel
end Erdos883Verified
