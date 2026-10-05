import Erdos883AdaptiveSpan27530Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength27530_7 : adaptiveNumericSpans27530_7.length = 462 := by decide +kernel
theorem adaptiveSpanEvenCache27530_7 : adaptiveSpanEven27530_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain27530_7 : adaptiveSpanEven27530_7.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanEvenEntries27530_7 : adaptiveSpanEven27530_7.spans = coreEvenSpans 13765 0 adaptiveNumericSpans27530_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache27530_7 : adaptiveSpanWhole27530_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain27530_7 : adaptiveSpanWhole27530_7.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanWholeEntries27530_7 : adaptiveSpanWhole27530_7.spans = coreWholeSpans 0 adaptiveNumericSpans27530_7 := by
  decide +kernel
end Erdos883Verified
