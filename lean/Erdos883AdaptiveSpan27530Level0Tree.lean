import Erdos883AdaptiveSpan27530Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength27530_0 : adaptiveNumericSpans27530_0.length = 462 := by decide +kernel
theorem adaptiveSpanEvenCache27530_0 : adaptiveSpanEven27530_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain27530_0 : adaptiveSpanEven27530_0.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanEvenEntries27530_0 : adaptiveSpanEven27530_0.spans = coreEvenSpans 13765 0 adaptiveNumericSpans27530_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache27530_0 : adaptiveSpanWhole27530_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain27530_0 : adaptiveSpanWhole27530_0.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanWholeEntries27530_0 : adaptiveSpanWhole27530_0.spans = coreWholeSpans 0 adaptiveNumericSpans27530_0 := by
  decide +kernel
end Erdos883Verified
