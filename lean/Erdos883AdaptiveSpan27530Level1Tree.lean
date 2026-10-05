import Erdos883AdaptiveSpan27530Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength27530_1 : adaptiveNumericSpans27530_1.length = 462 := by decide +kernel
theorem adaptiveSpanEvenCache27530_1 : adaptiveSpanEven27530_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain27530_1 : adaptiveSpanEven27530_1.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanEvenEntries27530_1 : adaptiveSpanEven27530_1.spans = coreEvenSpans 13765 0 adaptiveNumericSpans27530_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache27530_1 : adaptiveSpanWhole27530_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain27530_1 : adaptiveSpanWhole27530_1.domainCheck 13765 = true := by decide +kernel
theorem adaptiveSpanWholeEntries27530_1 : adaptiveSpanWhole27530_1.spans = coreWholeSpans 0 adaptiveNumericSpans27530_1 := by
  decide +kernel
end Erdos883Verified
