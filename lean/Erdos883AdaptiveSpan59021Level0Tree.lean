import Erdos883AdaptiveSpan59021Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength59021_0 : adaptiveNumericSpans59021_0.length = 555 := by decide +kernel
theorem adaptiveSpanEvenCache59021_0 : adaptiveSpanEven59021_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain59021_0 : adaptiveSpanEven59021_0.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries59021_0 : adaptiveSpanEven59021_0.spans = coreEvenSpans 29511 0 adaptiveNumericSpans59021_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache59021_0 : adaptiveSpanWhole59021_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain59021_0 : adaptiveSpanWhole59021_0.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries59021_0 : adaptiveSpanWhole59021_0.spans = coreWholeSpans 0 adaptiveNumericSpans59021_0 := by
  decide +kernel
end Erdos883Verified
