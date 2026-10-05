import Erdos883AdaptiveSpan27530Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength27530_2 : adaptiveNumericSpans27530_2.length = 462 := by decide +kernel
theorem adaptiveSpanEvenCache27530_2 : adaptiveSpanEven27530_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain27530_2 : adaptiveSpanEven27530_2.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanEvenEntries27530_2 : adaptiveSpanEven27530_2.spans = coreEvenSpans 13765 0 adaptiveNumericSpans27530_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache27530_2 : adaptiveSpanWhole27530_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain27530_2 : adaptiveSpanWhole27530_2.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanWholeEntries27530_2 : adaptiveSpanWhole27530_2.spans = coreWholeSpans 0 adaptiveNumericSpans27530_2 := by
  decide +kernel
end Erdos883Verified
