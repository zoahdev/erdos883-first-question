import Erdos883AdaptiveSpan71417Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength71417_5 : adaptiveNumericSpans71417_5.length = 581 := by decide +kernel
theorem adaptiveSpanEvenCache71417_5 : adaptiveSpanEven71417_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain71417_5 : adaptiveSpanEven71417_5.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanEvenEntries71417_5 : adaptiveSpanEven71417_5.spans = coreEvenSpans 35709 0 adaptiveNumericSpans71417_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache71417_5 : adaptiveSpanWhole71417_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain71417_5 : adaptiveSpanWhole71417_5.domainCheck 35709 = true := by decide +kernel
theorem adaptiveSpanWholeEntries71417_5 : adaptiveSpanWhole71417_5.spans = coreWholeSpans 0 adaptiveNumericSpans71417_5 := by
  decide +kernel
end Erdos883Verified
