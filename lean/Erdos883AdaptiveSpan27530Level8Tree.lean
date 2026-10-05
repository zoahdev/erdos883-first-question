import Erdos883AdaptiveSpan27530Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength27530_8 : adaptiveNumericSpans27530_8.length = 462 := by decide +kernel
theorem adaptiveSpanEvenCache27530_8 : adaptiveSpanEven27530_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain27530_8 : adaptiveSpanEven27530_8.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanEvenEntries27530_8 : adaptiveSpanEven27530_8.spans = coreEvenSpans 13765 0 adaptiveNumericSpans27530_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache27530_8 : adaptiveSpanWhole27530_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain27530_8 : adaptiveSpanWhole27530_8.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanWholeEntries27530_8 : adaptiveSpanWhole27530_8.spans = coreWholeSpans 0 adaptiveNumericSpans27530_8 := by
  decide +kernel
end Erdos883Verified
