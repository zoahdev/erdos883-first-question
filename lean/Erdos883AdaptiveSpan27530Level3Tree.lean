import Erdos883AdaptiveSpan27530Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength27530_3 : adaptiveNumericSpans27530_3.length = 462 := by decide +kernel
theorem adaptiveSpanEvenCache27530_3 : adaptiveSpanEven27530_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain27530_3 : adaptiveSpanEven27530_3.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanEvenEntries27530_3 : adaptiveSpanEven27530_3.spans = coreEvenSpans 13765 0 adaptiveNumericSpans27530_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache27530_3 : adaptiveSpanWhole27530_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain27530_3 : adaptiveSpanWhole27530_3.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanWholeEntries27530_3 : adaptiveSpanWhole27530_3.spans = coreWholeSpans 0 adaptiveNumericSpans27530_3 := by
  decide +kernel
end Erdos883Verified
