import Erdos883AdaptiveSpan27530Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength27530_5 : adaptiveNumericSpans27530_5.length = 462 := by decide +kernel
theorem adaptiveSpanEvenCache27530_5 : adaptiveSpanEven27530_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain27530_5 : adaptiveSpanEven27530_5.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanEvenEntries27530_5 : adaptiveSpanEven27530_5.spans = coreEvenSpans 13765 0 adaptiveNumericSpans27530_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache27530_5 : adaptiveSpanWhole27530_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain27530_5 : adaptiveSpanWhole27530_5.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanWholeEntries27530_5 : adaptiveSpanWhole27530_5.spans = coreWholeSpans 0 adaptiveNumericSpans27530_5 := by
  decide +kernel
end Erdos883Verified
