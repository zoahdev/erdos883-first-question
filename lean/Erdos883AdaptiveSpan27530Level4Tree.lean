import Erdos883AdaptiveSpan27530Level4TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength27530_4 : adaptiveNumericSpans27530_4.length = 462 := by decide +kernel
theorem adaptiveSpanEvenCache27530_4 : adaptiveSpanEven27530_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain27530_4 : adaptiveSpanEven27530_4.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanEvenEntries27530_4 : adaptiveSpanEven27530_4.spans = coreEvenSpans 13765 0 adaptiveNumericSpans27530_4 := by
  decide +kernel
theorem adaptiveSpanWholeCache27530_4 : adaptiveSpanWhole27530_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain27530_4 : adaptiveSpanWhole27530_4.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanWholeEntries27530_4 : adaptiveSpanWhole27530_4.spans = coreWholeSpans 0 adaptiveNumericSpans27530_4 := by
  decide +kernel
end Erdos883Verified
