import Erdos883AdaptiveSpan59021Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength59021_1 : adaptiveNumericSpans59021_1.length = 555 := by decide +kernel
theorem adaptiveSpanEvenCache59021_1 : adaptiveSpanEven59021_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain59021_1 : adaptiveSpanEven59021_1.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries59021_1 : adaptiveSpanEven59021_1.spans = coreEvenSpans 29511 0 adaptiveNumericSpans59021_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache59021_1 : adaptiveSpanWhole59021_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain59021_1 : adaptiveSpanWhole59021_1.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries59021_1 : adaptiveSpanWhole59021_1.spans = coreWholeSpans 0 adaptiveNumericSpans59021_1 := by
  decide +kernel
end Erdos883Verified
