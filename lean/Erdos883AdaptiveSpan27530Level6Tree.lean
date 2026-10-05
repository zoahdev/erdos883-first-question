import Erdos883AdaptiveSpan27530Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength27530_6 : adaptiveNumericSpans27530_6.length = 462 := by decide +kernel
theorem adaptiveSpanEvenCache27530_6 : adaptiveSpanEven27530_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain27530_6 : adaptiveSpanEven27530_6.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanEvenEntries27530_6 : adaptiveSpanEven27530_6.spans = coreEvenSpans 13765 0 adaptiveNumericSpans27530_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache27530_6 : adaptiveSpanWhole27530_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain27530_6 : adaptiveSpanWhole27530_6.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanWholeEntries27530_6 : adaptiveSpanWhole27530_6.spans = coreWholeSpans 0 adaptiveNumericSpans27530_6 := by
  decide +kernel
end Erdos883Verified
