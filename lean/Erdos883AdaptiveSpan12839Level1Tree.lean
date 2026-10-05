import Erdos883AdaptiveSpan12839Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength12839_1 : adaptiveNumericSpans12839_1.length = 385 := by decide +kernel
theorem adaptiveSpanEvenCache12839_1 : adaptiveSpanEven12839_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain12839_1 : adaptiveSpanEven12839_1.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanEvenEntries12839_1 : adaptiveSpanEven12839_1.spans = coreEvenSpans 6420 0 adaptiveNumericSpans12839_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache12839_1 : adaptiveSpanWhole12839_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain12839_1 : adaptiveSpanWhole12839_1.domainCheck 6420 = true := by decide +kernel
theorem adaptiveSpanWholeEntries12839_1 : adaptiveSpanWhole12839_1.spans = coreWholeSpans 0 adaptiveNumericSpans12839_1 := by
  decide +kernel
end Erdos883Verified
